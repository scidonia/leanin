import Std
import LeanIn.Task.Basic

/-!
# Async synchronisation: a mutex, a semaphore and a bounded channel

`docs/interface.md` §4: the task layer needs synchronisation primitives that park a *computation* without
parking the carrier. Three live here — an async mutex, an async semaphore and a bounded channel — behind the
surface the interface fixes: awaiting operations are `Async`, and operations that cannot park are `IO`.

**The mechanism is the task layer's own, and the one idea it turns on is that a wake is a hint, never a
hand-off.** A `Semaphore` is a permit count plus a waiter list, both under one `Std.Mutex`; a `Mutex` is a
semaphore of one permit; a `Channel` is a bounded FIFO queue with a sender list and a receiver list beside it.
An operation that cannot be served registers `{wake := fresh Join, token := ctx.cancel}` and, outside the
critical section, parks on that cell with `Join.onReady`; its continuation re-enters the same step through
`ctx.resume`, so the retry is a step stamped with the waiting computation's own token. A `release` — and a
`recv` that frees room, or a `send` that fills a slot — takes the **whole** waiter list it could satisfy, clears
it in the critical section, and resolves each taken cell with `Join.resolveFirst` *outside* the lock; the woken
waiter re-checks the state and, if it is still not satisfied, registers a **fresh** `Join` and parks again. So a
wake transfers nothing, and a wake that `Item.fire` skips — because the waiter's token was set meanwhile — is a
no-op: no permit moved, no message left the queue, and the cancelled waiter is never a holder.

**Why not adapt the stock shapes.** Both stock shapes hand what a waiter asked for to that waiter
*irrevocably*: `Std.Semaphore.release` dequeues a waiter and resolves the promise it parked on
(`Std/Sync/Semaphore.lean:76-87`), so a permit is gone whether or not the waiter ever runs again;
`Std.Channel.recv` dequeues the message into the task it returns (`Std/Sync/Channel.lean:542-546`), before any
awaiter is resumed. Our cancellation gate is `Item.fire` (`LeanIn/Task/Basic.lean:99-100`), and it skips a
cancelled computation's step — but it cannot un-resolve a promise or re-enqueue a dequeued message, so a waiter
whose token is set between the hand-off and the resumed step consumes a permit or a message and is never
granted it. That is the law a waiter must not violate: **a cancelled waiter is granted nothing and consumes
nothing.** The adapter route is rejected for exactly that reason; the mechanism above is what satisfies the
law, because the wake is revocable.

**Cancellation, per primitive.** A mutex or semaphore waiter's retry is stamped with the waiter's token by
`ctx.resume`, so `Item.fire` skips it, and its entry is pruned at the next operation; it was never granted
anything, so a cancelled acquirer consumes no permit and is never a holder. A channel sender's value enters
the queue only inside the sender's own step, and a receiver's dequeue only inside the receiver's own step, so a
cancelled sender enqueues nothing and consumes no slot and a cancelled receiver consumes no message. A
cancelled waiter's cell is still resolved (the wake was taken and cleared), but its step is skipped, which is a
no-op precisely because nothing was transferred. Nothing in `Hooks` changes: a sync waiter is a *computation*,
not a leaf registration — its wake is produced by another computation's step on the carrier — so there is
nothing to retire, and `Runtime.pending` does not count a parked lock waiter.

**What the interface promises, and what it deliberately does not.**

* **No fairness or priority.** The order in which waiters are admitted is unspecified, and the order in which a
  mutex's sections are taken is unspecified (`docs/interface.md` §5). The wake is broadcast (every parked
  waiter is resolved) and the waiters re-acquire in whatever order the carrier serves their steps; nothing here
  may be read as promising an order.
* **No RAII guard.** The mutex is an explicit `lock`/`unlock` pair. Lean has no drop hook that could release, so
  a guard would silently never release; guarding a value is the caller's business.
* **No owner or reentrancy check.** A mutex is a one-permit semaphore. It is not reentrant, and an `unlock` by a
  computation that did not `lock` is a defect this layer does not detect.
* **Capacity zero is refused, loudly.** A channel that can hold no value serves no sender, and a rendezvous
  between one sender and one receiver needs a different shape than a buffer; `Channel.new` throws and names the
  capacity rather than hand back a channel that can never be used.
* **Single-carrier, for now.** Every operation here is a step on one carrier, and the mechanism is a critical
  section over a `Std.Mutex` plus a registry-free waiter list. `Cancel.isSet` is read *inside* these critical
  sections — the only read is the private `live`, called under `st.state.atomically` — while the token's *write*
  (`Cancel.set`, from `Task.cancel`) is the unsynchronized half, taken under no state lock. That asymmetry is a
  pre-existing fact of the task layer and a race the moment a second carrier exists. A
  critical section is list and natural-number code only: an `await` inside one would wedge the carrier, and
  nothing `Async` is called under `atomically`.

**The bound is the caller's.** `Channel.new` takes its capacity as an argument, like `BlockingPool.new`'s width,
because the runtime has no configuration surface and a default bound would be an unstated policy. `send` parks
until there is room — that is the back-pressure — and `recv` parks until there is a message.
-/

namespace LeanIn.Task.Sync

/-- **A parked computation's cell, and the token that decides whether it is still wanted.** The cell is the
waiter's own fresh `Join`; a wake resolves it, and the continuation registered on it re-enters the operation's
step. The token is the waiting computation's, so a step enqueued after a cancellation is skipped by
`Item.fire`. -/
structure Waiter where
  /-- The cell this waiter parks on. A wake resolves it; resolving it transfers nothing. -/
  wake : Join Unit
  /-- The waiting computation's cancellation token, read when the entry is pruned. -/
  token : Cancel

/-- **Resolve every taken waiter, outside the state lock.** The list has already been cleared from the
primitive's state, so a resolution here only *schedules* a step — running a continuation while holding the
state lock would nest locks. `resolveFirst` because a wake is a hint and a second one for the same cell is not a
defect. -/
private def wakeAll (ws : List Waiter) : IO Unit :=
  for w in ws do Join.resolveFirst w.wake ()

/-- **The semaphore's state**: the permits available, and the computations parked for one. -/
structure SemState where
  /-- Permits currently available. A release adds one; a grant takes one. -/
  permits : Nat
  /-- Computations parked for a permit, oldest first. Order is not a guarantee. -/
  waiters : List Waiter

/-- **An async semaphore.** The mechanism itself: a permit count and a waiter list under one `Std.Mutex`. -/
structure Semaphore where
  state : Std.Mutex SemState

/-- **An async mutex**, as a semaphore of one permit. No guard, no owner check, not reentrant. -/
structure Mutex where
  sem : Semaphore

/-- **A bounded channel's state**: the FIFO queue and the two waiter lists.

The queue is a **two-list FIFO**. `front` is its read side and `back` its write side: a send prepends to `back`
(`v :: back`), a receive takes the head of `front`, and a receive that finds `front` empty first reverses `back`
into it (`front := back.reverse`, `back := []`). Each value is prepended once and moved by at most one reverse,
so **both ends are O(1) amortised** — no `++ [v]` append remains, and filling a channel of capacity `n` is
linear in messages rather than quadratic. `size` is the queue's occupancy (`size = front.length + back.length`),
tracked explicitly because `List.length` walks the list: recomputing it on every send would put the O(n) back
into the enqueue path and with it the quadratic fill. The bound is the separate `cap` count, never this
representation. -/
structure ChanState (α : Type) where
  /-- The queue's read side: buffered values, oldest at the head. -/
  front : List α
  /-- The queue's write side: buffered values, newest at the head, reversed into `front` when it empties. -/
  back : List α
  /-- The queue's occupancy, `front.length + back.length`, kept so the bound check is O(1). -/
  size : Nat
  /-- Senders parked because the queue was full. Order is not a guarantee. -/
  senders : List Waiter
  /-- Receivers parked because the queue was empty. Order is not a guarantee. -/
  receivers : List Waiter

/-- **A bounded channel.** The bound is the caller's argument; `cap = 0` is refused at `new`. -/
structure Channel (α : Type) where
  state : Std.Mutex (ChanState α)
  cap : Nat

/-- The waiters whose tokens are not yet set. Polymorphic in the monad so it can run inside a critical
section without a lift at the call site. A dying waiter is discovered the next time the primitive touches its
list, because a parked waiter holds no `Hooks` registration to retire. -/
private def live {m : Type → Type} [Monad m] [MonadLiftT BaseIO m] (ws : List Waiter) : m (List Waiter) :=
  ws.filterM fun w => do
    let gone ← liftM (w.token.isSet : BaseIO Bool)
    return !gone

namespace Semaphore

/-- A semaphore with `permits` available. -/
def new (permits : Nat) : IO Semaphore :=
  return ⟨← Std.Mutex.new { permits := permits, waiters := [] }⟩

/-- **The acquisition step**, and the retry a wake schedules. One critical section tries to take a permit; if
none is available the second registers a fresh `Join` and the computation parks on it. A wake only re-enters
this step, which re-reads the state: a wake is a hint, so nothing is transferred and a skipped wake costs
nothing. -/
private partial def acquireStep (s : Semaphore) (k : Unit → IO Unit) (ctx : Ctx) : IO Unit := do
  let ready ← s.state.atomically do
    let st ← get
    let ws ← live st.waiters
    if st.permits > 0 then
      set { st with permits := st.permits - 1, waiters := ws }
      return true
    else
      set { st with waiters := ws }
      return false
  if ready then
    k ()
  else
    -- The `Join` is made before the lock, so no lock is taken while holding another.
    let j : Join Unit ← Join.new
    let parked ← s.state.atomically do
      let st ← get
      let ws ← live st.waiters
      if st.permits > 0 then
        set { st with permits := st.permits - 1, waiters := ws }
        return false
      else
        set { st with waiters := ws ++ [Waiter.mk j ctx.cancel] }
        return true
    if parked then
      Join.onReady j (fun () => ctx.resume (Item.ofAction (acquireStep s k ctx)))
    else
      k ()

/-- Request a permit, parking the computation while none is available. -/
def acquire (s : Semaphore) : Task.Async Unit :=
  ⟨fun k ctx => acquireStep s k ctx⟩

/-- Take a permit if one is available, without parking. -/
def tryAcquire (s : Semaphore) : IO Bool :=
  s.state.atomically do
    let st ← get
    let ws ← live st.waiters
    if st.permits > 0 then
      set { st with permits := st.permits - 1, waiters := ws }
      return true
    else
      set { st with waiters := ws }
      return false

/-- **Return a permit, and wake the whole waiter list as a hint.** The list is taken and cleared inside the
lock and resolved outside it; each woken waiter re-checks the count, and a woken waiter that was cancelled
consumes nothing. -/
def release (s : Semaphore) : IO Unit := do
  let ws ← s.state.atomically do
    let st ← get
    set { st with permits := st.permits + 1, waiters := [] }
    return st.waiters
  wakeAll ws

end Semaphore

namespace Mutex

/-- A mutex is a semaphore of one permit. -/
def new : IO Mutex :=
  return ⟨← Semaphore.new 1⟩

/-- Acquire the mutex, parking the computation while it is held. -/
def lock (m : Mutex) : Task.Async Unit :=
  m.sem.acquire

/-- Release the mutex. Explicit, because there is no drop hook that could do it. -/
def unlock (m : Mutex) : IO Unit :=
  m.sem.release

/-- Take the mutex if it is free, without parking. -/
def tryLock (m : Mutex) : IO Bool :=
  m.sem.tryAcquire

end Mutex

namespace Channel

/-- Create a channel of capacity `cap`. Zero is refused: a channel with no room can serve no sender, and a
rendezvous needs a different shape than a buffer. The refusal names the capacity, as the blocking pool's `new`
names a zero width. -/
def new (α : Type) (cap : Nat) : IO (Channel α) := do
  if cap == 0 then
    throw (IO.userError s!"Sync.Channel.new: capacity {cap} leaves no room for a value, so a sender could \
      never be served; a rendezvous needs a different shape than a buffer")
  return { state := ← Std.Mutex.new { front := ([] : List α), back := [], size := 0, senders := [], receivers := [] }, cap := cap }

/-- The channel state with its cancelled waiters dropped. Polymorphic in the monad so it can run inside a
critical section without a lift at the call site. -/
private def prune {m : Type → Type} [Monad m] [MonadLiftT BaseIO m] (st : ChanState α) : m (ChanState α) := do
  let senders ← live st.senders
  let receivers ← live st.receivers
  return { st with senders := senders, receivers := receivers }

/-- **Enqueue**: prepend to the write side and count it, O(1). -/
private def enqueue (st : ChanState α) (v : α) : ChanState α :=
  { st with back := v :: st.back, size := st.size + 1 }

/-- **Dequeue**: take the head of the read side, reversing the write side into it when the read side has run
empty, and count it out. The reverse is the only non-constant step and each value takes it at most once, so
dequeue is O(1) amortised. -/
private def dequeue (st : ChanState α) : Option (α × ChanState α) :=
  match st.front with
  | v :: rest => some (v, { st with front := rest, size := st.size - 1 })
  | [] =>
    match st.back.reverse with
    | []         => none
    | v :: rest  => some (v, { st with front := rest, back := [], size := st.size - 1 })

/-- **The send step**, and the retry a wake schedules. The value is enqueued only inside this step — in the
served case it never parks; in the parked case a wake re-enters the step, which re-checks the room. A cancelled
sender's retry is skipped, so it enqueues nothing and consumes no slot. -/
private partial def sendStep (c : Channel α) (v : α) (k : Unit → IO Unit) (ctx : Ctx) : IO Unit := do
  let ready ← c.state.atomically do
    let st ← prune (← get)
    if st.size < c.cap then
      set { (enqueue st v) with receivers := [] }
      return some st.receivers
    else
      set st
      return none
  match ready with
  | some ws => wakeAll ws; k ()
  | none    =>
    let j : Join Unit ← Join.new
    let parked ← c.state.atomically do
      let st ← prune (← get)
      if st.size < c.cap then
        set { (enqueue st v) with receivers := [] }
        return some st.receivers
      else
        set { st with senders := st.senders ++ [Waiter.mk j ctx.cancel] }
        return none
    match parked with
    | some ws => wakeAll ws; k ()
    | none    => Join.onReady j (fun () => ctx.resume (Item.ofAction (sendStep c v k ctx)))

/-- Send a value, parking the computation while the channel is full. -/
def send (c : Channel α) (v : α) : Task.Async Unit :=
  ⟨fun k ctx => sendStep c v k ctx⟩

/-- Send a value if there is room, without parking. A send that finds room enqueues and wakes the receivers as
a hint; one that finds none returns `false` and wakes no one. -/
def trySend (c : Channel α) (v : α) : IO Bool := do
  let r ← c.state.atomically do
    let st ← prune (← get)
    if st.size < c.cap then
      set { (enqueue st v) with receivers := [] }
      return some st.receivers
    else
      set st
      return none
  match r with
  | some ws => wakeAll ws; return true
  | none    => return false

/-- **The receive step**, and the retry a wake schedules. The dequeue happens only inside this step, so a
cancelled receiver's retry is skipped and the message stays in the queue or goes to another receiver. -/
private partial def recvStep (c : Channel α) (k : α → IO Unit) (ctx : Ctx) : IO Unit := do
  let ready ← c.state.atomically do
    let st ← prune (← get)
    match dequeue st with
    | some (v, st') =>
      set { st' with senders := [] }
      return some (v, st.senders)
    | none =>
      set st
      return none
  match ready with
  | some (v, ws) => wakeAll ws; k v
  | none         =>
    let j : Join Unit ← Join.new
    let parked ← c.state.atomically do
      let st ← prune (← get)
      match dequeue st with
      | some (v, st') =>
        set { st' with senders := [] }
        return some (v, st.senders)
      | none =>
        set { st with receivers := st.receivers ++ [Waiter.mk j ctx.cancel] }
        return none
    match parked with
    | some (v, ws) => wakeAll ws; k v
    | none         => Join.onReady j (fun () => ctx.resume (Item.ofAction (recvStep c k ctx)))

/-- Receive a value, parking the computation while the channel is empty. -/
def recv (c : Channel α) : Task.Async α :=
  ⟨fun k ctx => recvStep c k ctx⟩

/-- Take a value if one is waiting, without parking. A dequeue frees room, so the senders are woken as a hint. -/
def tryRecv (c : Channel α) : IO (Option α) := do
  let r ← c.state.atomically do
    let st ← prune (← get)
    match dequeue st with
    | some (v, st') =>
      set { st' with senders := [] }
      return some (v, st.senders)
    | none =>
      set st
      return none
  match r with
  | some (v, ws) => wakeAll ws; return some v
  | none         => return none

end Channel

end LeanIn.Task.Sync
