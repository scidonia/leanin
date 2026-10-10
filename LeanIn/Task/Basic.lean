import Std
import LeanIn.Sched.Executor

/-!
# The task layer

`docs/interface.md` §4: our own `Task`/`Async`, because `Std.Async` cannot be reused — it is
`BaseIO (MaybeTask α)` and every operation delegates to `Task`, so it cannot be driven on one carrier.

Three pieces:

* `Item` is what the executor holds: one step of some computation, ready to run.
* `Async α` is a **scheduleable computation**, in continuation-passing style: `step k ctx` runs it until it
  either finishes — calling `k` — or reaches something it must wait for, in which case it registers a
  continuation and returns. It never blocks the thread, which is what makes a single carrier enough.
* `Task α` is the **handle**: the cell its value lands in, and where an awaiter leaves its continuation.

`resume` is *how to schedule*, and it is one function for two jobs: continuing a computation that yielded, and
starting a child. That is why this layer needs no executor of its own — the runtime supplies the function and
decides whether scheduling means the local slot or the shared queue.

**Awaiting is the O3 seam turned inward.** An external event is "attach a continuation that pushes into the
queue and notifies"; here the event is our own task finishing, and the continuation an awaiter leaves is pushed
back onto the executor the same way. So there is one path, whether the completer is this task, another task, or
a stock `Task` on a pool worker — and that path never runs anything on the completing thread.

**The name collides with core's `Task`, but only inside this library.** `LeanIn.Task` shadows `_root_.Task` for
files under `LeanIn/`, so code in this tree that wants the stock one — `IO.asTask`'s `Task.Priority.dedicated`
in the test clients — spells it `_root_.Task`. The interface names these two types, so the collision comes with
the interface rather than from the layout.
-/

namespace LeanIn.Task

/-- **A computation's cancellation token.** One flag, with the two operations a cancellation needs: `set`, which
is what requesting one does, and `isSet`, which is what a step asks before running.

The id is here so that a question can be asked *about one computation* — how many registrations it still holds —
rather than about the runtime, whose total includes every other computation's and is not stable at the moment of a
read. `BaseIO` and not `IO` for the flag, because the read happens on a step's path and scheduling is `BaseIO`;
idempotent, because a cancellation is a request rather than a state transition, so a second one is not a defect. -/
structure Cancel where
  flag : IO.Ref Bool
  id : Nat

namespace Cancel

/-- The token allocator, module-level because a token is made wherever a computation is spawned, by code that owns
no runtime. The read and the write are not atomic: with one carrier every spawn runs on that carrier, so nothing
interleaves them, and a second carrier is where this becomes a race to fix rather than a comment to keep. An id
only has to distinguish the tokens alive at one moment. -/
initialize counter : IO.Ref Nat ← IO.mkRef 0

def new : IO Cancel := do
  let n ← counter.get
  counter.set (n + 1)
  return ⟨← IO.mkRef false, n⟩

def set (c : Cancel) : BaseIO Unit := c.flag.set true

def isSet (c : Cancel) : BaseIO Bool := c.flag.get

end Cancel

/-- **One unit of scheduled work**: a step of some computation, ready to run. Named rather than a bare
`IO Unit` so that the executor's item type has an `Inhabited` instance, which the pool's ghost view needs. -/
structure Item where
  /-- The token of the computation this step belongs to, or `none` for a step no cancellation reaches — the
  driver's, or one submitted straight to an executor. -/
  cancel : Option Cancel
  /-- The action this step runs, when it is not cancelled. -/
  act : IO Unit

instance : Inhabited Item := ⟨⟨none, pure ()⟩⟩

/-- **This step, stamped with a token if it does not have one.**

A step built inside a computation is bare, so the first stamping function it meets is its own computation's, and
the ones it meets afterwards leave it alone. That ordering is what gives the identities: an item a computation
enqueues belongs to that computation, and an item it hands to its parent's function keeps the inner token. -/
def Item.stamp (it : Item) (c : Cancel) : Item :=
  match it.cancel with
  | some _ => it
  | none   => { it with cancel := some c }

/-- **A step before its computation stamps it.** -/
def Item.ofAction (act : IO Unit) : Item := ⟨none, act⟩

/-- **Whether this step is cancelled.** -/
def Item.cancelled (it : Item) : IO Bool :=
  match it.cancel with
  | some c => c.isSet
  | none   => return false

/-- **Run a step.** The check is here, at the one place every carrier runs a step through, so a cancelled
computation's steps are skipped whether they were enqueued before the cancellation or after it — the difference
between this and a flag the computation itself has to poll. Skipping is not running a no-op: nothing of the
computation executes. -/
def Item.fire (it : Item) : IO Unit := do
  unless ← it.cancelled do it.act

/-- **The join cell**: what a handle is. The value once there is one, and the continuations left by whoever
awaited it before then.

One lock, because the resolver and the awaiter can be different threads — and here they usually are: the
resolver is whoever finished the task, the awaiter is a carrier that yielded. -/
structure Join (α : Type) where
  lock : Std.Mutex (Option α × List (α → IO Unit))

def Join.new : IO (Join α) := return ⟨← Std.Mutex.new (none, [])⟩

/-- **Resolve**, running whoever was waiting.

Inside the lock the value goes in and the waiting continuations come out; outside it they run. Running them
inside would mean enqueuing — which takes the executor's lock — while holding this one, and two locks in one
path is how a runtime acquires a lock order nobody chose.

Resolving twice is a defect rather than a race to be tolerated, so it is loud: a handle is resolved by the one
computation that owns it, exactly once, and a second resolution means two writers. -/
def Join.resolve (j : Join α) (v : α) : IO Unit := do
  let ks ← j.lock.atomically do
    let st ← get
    match st.1 with
    | some _ => throw (IO.userError "Join.resolve: a task was resolved twice")
    | none   => set (some v, ([] : List (α → IO Unit))); return st.2
  for k in ks do k v

/-- **Resolve unless it is already resolved**: the first writer wins and a later one is *ignored* rather than a
defect.

Separate from `resolve` on purpose, and the difference is a law rather than a convenience. `resolve` states
that a handle has one writer, and is loud when that is broken; this states that several writers may race and
the result is the first of them, which is what a timeout or a `select`-shaped operation needs and what a
computation which is simply finishing normally must not rely on. -/
def Join.resolveFirst (j : Join α) (v : α) : IO Unit := do
  let ks? ← j.lock.atomically do
    let st ← get
    match st.1 with
    | some _ => return none
    | none   => set (some v, ([] : List (α → IO Unit))); return some st.2
  match ks? with
  | some ks => for k in ks do k v
  | none    => pure ()

/-- **Register, or run now.** An awaiter that arrives after the value did must not be left waiting: it runs
immediately, which is also what makes awaiting a finished handle return at once instead of yielding. -/
def Join.onReady (j : Join α) (k : α → IO Unit) : IO Unit := do
  let now? ← j.lock.atomically do
    let st ← get
    match st.1 with
    | some v => return some v
    | none   => set (st.1, st.2 ++ [k]); return none
  match now? with
  | some v => k v
  | none   => pure ()

/-- **What a computation carries ambiently, and its children inherit.** A request id, a deadline and a tracing
context — the values a log line or a deadline check reads without every signature between them gaining a
parameter. Nothing in the task layer or the runtime reads these fields: the runtime schedules, and a caller's log
line or a caller's deadline check reads them.

A typed record rather than a heterogeneous store keyed by name: a reader and a writer of a key agree by type
rather than by convention, and the value is one immutable copy a child takes at its spawn site rather than a map
behind a second lock. -/
structure Local where
  /-- The request this computation belongs to, or zero for none. -/
  requestId : Nat := 0
  /-- An absolute monotonic-nanosecond instant, or none. Nothing here reads it; W13's clock decides it. -/
  deadline : Option Nat := none
  /-- A tracing context: the one string a log line quotes. -/
  trace : String := ""

/-- **What a step is given**: its own cancellation token, and how to schedule an item.

Both travel together and mean the same thing — the computation is what a cancellation stops and what a
registration belongs to — so they are one parameter rather than two. The token being a *field* here is what lets a
leaf await attribute its registration to the computation that is waiting, which is the difference between a
registry that can be retired and one that can only grow.

`local` carries the ambient context too, and is what `Async.withLocal` reads: a computation's steps read it from
the parameter they already hold, so no signature gains one. It has no default, so every `Ctx` construction site
states it and the inheritance rule is a reviewed line rather than a silent omission. -/
structure Ctx where
  /-- The token of the computation this step belongs to. -/
  cancel : Cancel
  /-- Schedule an item — the local route, so a chain stays on the core its parent ran on. -/
  resume : Item → BaseIO Unit
  /-- The ambient context, inherited by a spawned child from its parent. -/
  «local» : Local

/-- **A scheduleable computation.**

`step k ctx` runs the computation until it finishes, calling `k` with the value, or until it must wait, in
which case it registers a continuation and returns. `bind` composes the continuations, so a resumed
computation continues from where it yielded rather than from its beginning — the difference between this and a
bare `Job`, which is a value that must be re-run.

The scheduling half of `ctx` is `BaseIO` rather than `IO`, and that is the O3 seam showing through: the one place a
schedule call has to happen is *inside a waker* — a continuation registered on a stock `Task`, running on a pool
worker — and a waker cannot call `IO`. Enqueuing takes a lock and notifies a condvar, so `BaseIO` is all it needs,
and the runtime's `resumeOf` is that function. -/
structure Async (α : Type) where
  step : (α → IO Unit) → Ctx → IO Unit

instance : Inhabited (Async α) := ⟨⟨fun _ _ => pure ()⟩⟩

instance : Monad Async where
  pure v   := ⟨fun k _ => k v⟩
  bind a f := ⟨fun k ctx => a.step (fun v => (f v).step k ctx) ctx⟩

/-- Run an `IO` action as a step of a computation. This is the inside of `interface.md` §4's one bridge: a leaf
operation — a timer, a socket, a stock `Task` — arrives as an action, and what keeps it non-blocking is that
whoever completes it schedules the continuation instead of running it here. -/
def Async.ofIO (act : IO α) : Async α := ⟨fun k _ => do k (← act)⟩

instance : MonadLift IO Async where monadLift act := Async.ofIO act

/-- **Read the ambient context.** A field read of the immutable `Ctx` the step was already given — no lock, no
lookup, and no signature between the reader and its caller gains a parameter. -/
def Async.«local» : Async Local := ⟨fun k ctx => k ctx.«local»⟩

/-- **Run a computation under a local context.** The value is installed on the `Ctx` this computation's steps run
with; a `spawn` inside it therefore builds the child's `Ctx` from a parent that already carries it, which is how
the child inherits the innermost enclosing value at its spawn site. -/
def Async.withLocal (l : Local) (a : Async α) : Async α :=
  ⟨fun k ctx => a.step k { ctx with «local» := l }⟩

/-- **A handle** on a spawned computation: the cell its value lands in, and its cancellation token. -/
structure Task (α : Type) where
  cell : Join α
  /-- Set by `Task.cancel`. Every step of this computation reads it before running, and every registration the
  computation leaves behind is attributed to it. -/
  token : Cancel

/-- **Cancel a handle's computation**: its token is set, so `Item.fire` skips its steps from now on, and its cell
is resolved with `v` through `resolveFirst`.

`resolveFirst` is the law for this race rather than `resolve`: `resolve` states that a handle has one writer and is
loud when that is broken, while here a computation finishing and a cancellation arriving genuinely race, and the
first of them is the result. So a computation that has already produced its value keeps it — a cancellation never
replaces a value that exists — and a cancellation that arrives first is delivered exactly once and immediately,
rather than leaving an awaiter parked forever on a value that will never come.

`v` is the caller's because this layer has no error of its own to give: `EAsync`'s handles are `Task (Except ε α)`,
so a server passes `.error (.userError "…")`.

Retiring the computation's registrations is not here but in the runtime, which is where the registry is. -/
def Task.cancel (t : Task α) (v : α) : IO Unit := do
  t.token.set
  Join.resolveFirst t.cell v

/-- **Start a computation on the current worker.** The child's first step is enqueued through `resume`, which
is the local route, so a chain of spawns stays on the core its parent ran on.

The child's items are stamped by its own scheduling function before its parent's sees them, and `Item.stamp` only
fills an empty field — so the child's first step already carries the *child's* token by the time the parent's
function sees it. Cancelling the parent therefore does not stop the child, whether it has started or not: every
spawned computation is cancellable on its own, which is `abort` rather than structured cancellation. A computation
that wants its children to stop with it has to cancel them. -/
def Async.spawn (a : Async α) : Async (Task α) := ⟨fun k ctx => do
  let cell ← Join.new
  let cancel ← Cancel.new
  let child : Ctx := { cancel := cancel, resume := fun it => ctx.resume (it.stamp cancel), «local» := ctx.«local» }
  child.resume (Item.ofAction (a.step (fun v => Join.resolve cell v) child))
  k ⟨cell, cancel⟩⟩

/-- **The value, if it is already there.** -/
def Join.value? (j : Join α) : IO (Option α) := j.lock.atomically do return (← get).1

/-- **Await.** If the value is already there, `k` is called now and the step does not yield: awaiting a
finished handle costs a lock and no scheduling round, which is what a `JoinHandle` polled as ready does.
Otherwise the continuation left behind *schedules itself* when the value arrives, and `step` returns without
calling `k`.

Reading then registering is not a race: if the value arrives between the two, `onReady` runs the continuation
immediately, which is the case it exists for. -/
def Async.await (t : Task α) : Async α := ⟨fun k ctx => do
  match ← t.cell.value? with
  | some v => k v
  | none   => Join.onReady t.cell (fun v => ctx.resume (Item.ofAction (k v)))⟩

/-- **The first of several handles to become ready.**

Homogeneous and non-empty: `h` is the head, so index `0` names it and index `i+1` names `hs[i]`; a zero-handle
`select` is unrepresentable rather than a meaningless `none`. It returns the winner's index into the list as
given and its value, and it does not cancel its losers — a handle passed to `select` is still awaitable
elsewhere.

Among handles already resolved when `select` is reached, the earliest in list order wins; among handles resolved
while `select` waits, the first resolution wins. -/
def select (h : Task α) (hs : List (Task α)) : Async (Nat × α) := ⟨fun k ctx => do
  let j ← (Join.new : IO (Join (Nat × α)))
  -- One registration per handle, each carrying its index. `Join.onReady` runs a continuation immediately when
  -- the handle is already resolved, so an already-satisfiable `select` resolves `j` during this loop, in list
  -- order — the tie rule for handles resolved before the call.
  let rec go : List (Task α) → Nat → IO Unit
    | [], _ => pure ()
    | t :: ts, i => do
        Join.onReady t.cell (fun v => Join.resolveFirst j (i, v))
        go ts (i + 1)
  go (h :: hs) 0
  -- Mirror `Async.await`: a value already in the shared cell (a handle resolved during the loop) is returned
  -- in-step with no scheduling round; otherwise the step parks on the shared cell.
  match ← Join.value? j with
  | some w => k w
  | none   => Join.onReady j (fun w => ctx.resume (Item.ofAction (k w)))⟩

/-- **Wait for every handle, in list order.** `join [] = pure []`, and the pair case stays `concurrently`. -/
def join (hs : List (Task α)) : Async (List α) := hs.mapM Async.await

/-- **What generic code is written against**: joining and starting, with the handle type alongside. -/
class MonadAwait (m : Type → Type) where
  /-- The handle type: what starting a computation in `m` gives you. -/
  Handle : Type → Type
  /-- Wait for a handle's value. -/
  await : Handle α → m α

/-- Anything that can also start computations. -/
class MonadAsync (m : Type → Type) extends MonadAwait m where
  /-- Start a computation on the current worker. -/
  spawn : m α → m (Handle α)

instance : MonadAwait Async where
  Handle := Task
  await  := Async.await

instance : MonadAsync Async where
  spawn := Async.spawn

/-- Run both and return both values. Concurrent in the sense that matters: both are scheduled before either is
awaited. Written once, against the class, so any implementation of it gets this for free. -/
def concurrently [Monad m] [MonadAsync m] (a b : m α) : m (α × α) := do
  let ha ← MonadAsync.spawn a
  let hb ← MonadAsync.spawn b
  let va ← MonadAwait.await ha
  let vb ← MonadAwait.await hb
  return (va, vb)

/-- Run it and drop the handle: still scheduled, nothing waits for it. -/
def background [Monad m] [MonadAsync m] (a : m α) : m Unit := do
  let _ ← MonadAsync.spawn a
  return ()

end LeanIn.Task
