module

public import Std
public import LeanIn.Data.Deque
public import LeanIn.Sched.Pool
public import LeanIn.Model.Multi
public import LeanIn.Sched.Scheduler


public import Std.Sync.Mutex
public section
-- `Pool` is built on `Ring`, whose operations need `Inhabited α` (`toList` falls back to `default`), so
-- anything holding a `Pool` needs the instance in scope. Carried once here rather than at each mention.
set_option linter.unusedSectionVars false

/-!
# The executor at P carriers

`Sched.Pool` is one worker's queue and `Sched.Scheduler` is the wake protocol's abstract state; this file is
where a *set* of them is held together, and the shape follows from one decision: **a worker's queue is its
own, and the inject is shared**. So there is one `Std.Mutex` per worker's pool and one for the shared cell
holding the inject's items *and* the idle bookkeeping — the parked count, the carrier count and the stopping
flag. The parked count lives with the inject's contents because a push that must unpark and a park that must
re-check the inject are then the *same* critical section: that is what makes a cross-carrier wake impossible
to lose between the check and the wait.

## The critical sections, per queue

| queue | lock | transactions |
|---|---|---|
| worker `i`'s pool | that pool's own mutex | take slot/flush/ring; a local submit into the ring; a local spawn into the slot; the tick; one thief's steal; a metrics read |
| the shared inject and its idle counters | the inject's own mutex | push one and unpark one parked worker; pop one; park (re-check the inject, record the park, wait); stop (set the flag, notify all); a metrics read |

**Lock order: pool → inject, everywhere.** The paths that take both are a local push whose placement
overflows and a take whose allowance has run out with the slot occupied; each takes its pool first. Nothing
takes the inject and then a pool, so two locks is the most any path holds and the order is total.

## Which worker, and what a worker is

`Executor.workerLoop e fire i` is one carrier's shift: take from worker `i`'s own queue, then one steal
attempt, then the shared list; park when all three are empty. `fire` is the caller's, because what an item
*is* and how it is run belong to the layer above this one — the runtime passes `Item.fireWith` and the
worker's own route. The driver's path (`run`/`blockOn`) is worker `0`'s loop run **on the calling thread**,
through the same operations, which is why no existing scenario's driver changed.

`Executor.submit`/`spawn`/`take`/`takeReport`/`tick`/`work` are the driver's spelling of worker `0`'s
operations: the calling thread stands in for worker `0`, so a single-carrier path takes the same critical
sections a carrier does.

## The local route, and why a local push owes no wake

A push a step makes on its own worker is the owner's, and the owner is running the step that makes it, so it
owes no wake — and after the route rebinding it is the *only* kind of local push there is. A step's own
re-enqueue takes the route of the worker firing it (`Ctx.resume`), and every resume that is not a step's own —
the two seam completions (`Runtime/Leaf.lean`'s leaf continuations and `Runtime/Blocking.lean`'s blocking
completion), the harness clock's fire, `Runtime.Handle.spawn`, the root pushes — takes the **shared** route,
whose push appends to the inject and unparks a parked waiter *inside that section* (`Executor.pushItems`). So
nothing outside a worker's own step writes that worker's queue, which is the model's `pushLocal` premise
(`docs/interface.md`'s obligation table) as an implementation fact rather than a convention.

**This section is history, kept because it is what the code used to do.** The third off-owner local push —
`LeanIn/Task/Basic.lean`'s `Async.await` and `select`, which registered `ctx.resume` on a `Join` cell and had
it run on whichever carrier resolved the cell — was covered by a per-worker wake flag recorded in the shared
cell plus a broadcast, so the owner was among the woken. It is gone with the rebinding, and the per-push
section that local pushes paid for it went with it (`spawnLocalRaw`/`submitLocalRaw` now make one pool
transaction and nothing else). `docs/decisions.md`'s D22 records the mechanism by name. Routing that site
through `resumeShared` instead was rejected then and stays rejected: the route on the cell is the awaiter's but
the continuation runs on the resolver, so a shared route would send every await continuation through the shared
list and let a chain cross a carrier on a tree where nothing was stolen.

The parallel entry starts `p` dedicated carriers and submits the program's root to the shared list, and the
caller **only waits** on the program's completion (`Runtime.runCarriers`, `Executor.waitFinished`); it does
not run worker `0`'s loop, because worker `0` already has a carrier thread.

## What a transient write does to a count

Every transaction that changes a pool's held work composes with the pool's own count laws
(`Pool.toRing_inFlight`, `Pool.take_inFlight`, `Pool.flushSlot_inFlight`): the flush is the only path where
an item *leaves* the pool without being taken, and the append the flush performs on the shared list is what
completes its accounting.
-/

namespace LeanIn.Sched

variable {α : Type} [Inhabited α]

/-- **What a worker's fire supplies**: how to enqueue an item on the worker that is firing. The step's body
receives it at fire time, which is what makes a chain follow the worker that ran its parent rather than the
worker that spawned it.

A structure rather than a bare function type, and that is a typing fact rather than taste: a field whose type
is a function *mentioning the item type in its domain* — `act : (Item → BaseIO Unit) → IO Unit` — is a
non-positive occurrence, and Lean refuses to declare the item at all. A structure applied to the item type is
positive, so the route is one, and `enqueue` is the function. -/
structure Route (α : Type) where
  /-- Enqueue an item on the worker that supplied this route. -/
  enqueue : α → BaseIO Unit

/-- The route a function gives: the shape a caller that already has the enqueue function uses. -/
def Route.ofFn {α : Type} (f : α → BaseIO Unit) : Route α := ⟨f⟩

/-- What one carrier has fired, the thread it ran on, and the nanoseconds of the installed clock it spent
inside them.

Measured only by a metered executor, and a duration needs a clock: under the live clock this is
`IO.monoNanosNow`, under a driver's virtual clock it is virtual nanoseconds, which do not advance while work
runs. So `busyNanos` is a reading to print rather than a quantity to assert. The `tid` is recorded once, when
the carrier starts, which is what makes "which carriers ran anything" readable without the client keeping its
own log. -/
structure CarrierCounters where
  /-- The carrier's thread id, recorded at the start of its shift. -/
  tid       : UInt64 := 0
  /-- Items this carrier ran. -/
  fired     : Nat := 0
  /-- Nanoseconds of the installed clock spent inside them. -/
  busyNanos : Nat := 0
deriving Inhabited, Repr

/-- **The shared cell**: the inject's items and the idle bookkeeping, under one lock.

`served` is what this cell has handed out, so the composition's own take count is the sum of the places an
item can be taken from — every worker's pool, and here. -/
structure InjectState (α : Type) where
  /-- The shared queue: external wakes and every worker's overflow. Unbounded. -/
  items    : Deque α := {}
  /-- Waiters parked now: every wait records itself — the carriers and the calling-thread driver alike — and
  this is the count a push tests before it notifies one of them. -/
  parked   : Nat := 0
  /-- Carriers in total. Constant: carriers neither arrive nor leave. -/
  total    : Nat := 0
  /-- Set by `stop`. -/
  stopping : Bool := false
  /-- Items this cell has served. -/
  served   : Nat := 0
  /-- **The driver's own stop condition, in the cell it waits on.**

A wait whose predicate omits the condition it waits *for* is the same defect class as a missing wake: the
driver parks on this cell, and the program's last step may run on a carrier, so nothing else can make the top
of the driver's loop reachable again. The completion records itself here and notifies in one section, and the
driver's predicate reads it in the same section as the shared list — one cell, S1's discipline, no second lock
and so no second order. A *further refusal* on a park cannot lose a wakeup (`Live` is monotone in refusals),
so the model's `park` premise is untouched. One driver per executor, so one flag. -/
  finished : Bool := false
deriving Inhabited

/-- The composition's own accounting, as one reading: every worker's pool, the shared list, and the two
counters that say what has left. `held` is the same sum the model's `Multi.held` is, which is what makes a
record read through it a reading of the specification's own quantity rather than a second count. -/
structure Snapshot (α : Type) (cap : Nat) where
  /-- Every worker's pool, read under its own lock. -/
  workers      : List (Pool α cap)
  /-- The shared list's contents, oldest first. -/
  inject       : List α
  /-- What the shared cell has served. -/
  injectServed : Nat
  /-- Waiters parked now, each wait having recorded itself. -/
  parked       : Nat
  /-- Carriers in total. -/
  total        : Nat
  /-- Set by `stop`. -/
  stopping     : Bool

/-- Work ready to be taken anywhere: every worker's own queue plus the shared list. -/
def Snapshot.held (s : Snapshot α cap) : Nat :=
  (s.workers.map Pool.inFlight).sum + s.inject.length

/-- Work taken so far: what the workers served plus what the shared cell did. -/
def Snapshot.taken (s : Snapshot α cap) : Nat :=
  (s.workers.map Pool.taken).sum + s.injectServed

/-- **The projection onto the model.** The same composition `Model.Multi` describes, with the park flags
rebuilt from the count the cell keeps. -/
def Snapshot.toModel (s : Snapshot α cap) : Model.Multi α cap :=
  { workers  := s.workers.map Pool.toModel
    inject   := { items := s.inject }
    -- `parked` counts waiters, and the driver that waits on the shared cell is not a carrier, so a parked
    -- driver can carry the count past the carrier count; the model's flags are one per carrier, and `min`
    -- keeps the list that length (`total - parked` saturates to zero past the end).
    parked   := List.replicate (min s.parked s.total) true ++ List.replicate (s.total - s.parked) false
    stopping := s.stopping
    pushed   := s.held + s.taken
    taken    := s.taken }

/-- An executor: one mutex per worker's pool, one over the shared cell, and one condvar every park waits
on. -/
structure Executor (α : Type) (cap : Nat) where
  private mk ::
  /-- One pool per carrier, each behind its own lock. -/
  private workers           : Array (Std.Mutex (Pool α cap))
  /-- The shared list and the idle counters. The *cell* says a carrier is parked; only the condvar makes a
  thread sleep, and a push notifies under the same lock a park re-checks its predicate under. -/
  private inject            : Std.Mutex (InjectState α)
  private cv                : Std.Condvar
  /-- Whether a carrier accumulates `counters`. Off for `Executor.new`, on for a metered executor: the
  default item path pays one test of this field and neither a lock nor a clock read. -/
  private metered           : Bool
  /-- Per-carrier accumulators, one entry per carrier, index `i` for worker `i`. Written by a carrier when
  it starts and around each item it runs, and read by a metrics read; a read copies a few scalars per
  carrier, mutates nothing and notifies nobody, so it cannot perturb what it measures. -/
  private counters          : Std.Mutex (List CarrierCounters)
  /-- The value a worker index that is out of range resolves to. `Array.getD` is the total accessor and an
  array of mutexes has no default, so the fallback exists; every index this file resolves is taken modulo
  the carrier count, so it is never the cell a transaction runs on. -/
  private spare             : Std.Mutex (Pool α cap)
  /-- **What a transaction writes into a pool's cell while it holds that pool's lock.**

Writing this value releases the cell's hold on the pool the transaction read, which is necessary for an in-place
ring write and not sufficient. It helps only while the cell is unshared: once another thread can reach the cell,
every value stored in it is marked multi-threaded, a marked array is never exclusive, and each ring write copies
the `cap` slots regardless. That is the state a running carrier's pool is in, and the cost is bounded by `cap`,
which is why the ring can afford it and the unbounded inject could not (`Data/Deque.lean`). Nothing outside the
critical section can see the placeholder: the lock is held for the whole transaction, and the value the
transaction computes is written back before the lock is released. -/
  poolPlaceholder   : Pool α cap

/-- **Replace the entry at index `i`**, leaving a list that is too short alone. Written out rather than taken
from core because the per-carrier list is indexed by worker number and a partial list must not be a defect. -/
def countersAt (i : Nat) (f : CarrierCounters → CarrierCounters) : List CarrierCounters → List CarrierCounters
  | [] => []
  | c :: rest => match i with
    | 0 => f c :: rest
    | n + 1 => c :: countersAt n f rest

def Executor.new (α : Type) (cap : Nat) (workers : Nat) : IO (Executor α cap) := do
  -- A pool per carrier, and never zero: every transaction resolves its worker index modulo this count, so an
  -- empty array would leave the driver with nothing to run on.
  let n := max 1 workers
  let mut ws : Array (Std.Mutex (Pool α cap)) := #[]
  for _ in List.range n do
    ws := ws.push (← Std.Mutex.new (emptyPool α cap))
  return { workers           := ws
           inject            := ← Std.Mutex.new
             { items := {}, parked := 0, total := n, stopping := false, served := 0 }
           cv                := ← Std.Condvar.new
           metered           := false
           counters          := ← Std.Mutex.new ((List.range n).map (fun _ => ({} : CarrierCounters)))
           spare             := ← Std.Mutex.new (emptyPool α cap)
           poolPlaceholder   := emptyPool α cap }

/-- How many carriers this executor was built with. -/
def Executor.workerCount (e : Executor α cap) : Nat := e.workers.size

/-- **Whether this executor accumulates per-carrier counters.** A read of the one flag the item path tests. -/
def Executor.isMetered (e : Executor α cap) : Bool := e.metered

/-- **Accrue a carrier's busy time**, for the driver's own metered path: one counters section. -/
def Executor.accrueAt (e : Executor α cap) (i : Nat) (busy : Nat) : IO Unit :=
  e.counters.atomically do
    let cs ← get
    set (countersAt i (fun c => { c with fired := c.fired + 1, busyNanos := c.busyNanos + busy }) cs)

/-- **An executor that accumulates per-carrier counters.** `Executor.new` leaves metering off. -/
def Executor.newMetered (α : Type) (cap : Nat) (workers : Nat) : IO (Executor α cap) := do
  let e ← Executor.new α cap workers
  return { e with metered := true }

/-- Worker `i`'s lock, taken modulo the carrier count so a caller cannot index past the array. -/
def Executor.cell (e : Executor α cap) (i : Nat) : Std.Mutex (Pool α cap) :=
  if h : i % e.workers.size < e.workers.size then e.workers[i % e.workers.size]'h else e.spare

/-! ### The shared cell's transactions -/

/-- **Append to the shared list and unpark one parked carrier**, in the one section every cross-carrier wake
passes through.

The items are the overflow of a placement or the task a flush cleared out of a slot; either way they are
appended here rather than written into a pool, because the list is shared. -/
def Executor.pushItems (e : Executor α cap) (xs : List α) : BaseIO Unit :=
  e.inject.atomically do
    let st ← get
    set { st with items := xs.foldl (fun d x => d.push x) st.items }
    if 0 < st.parked then e.cv.notifyOne

/-- Push one item into the shared list, across a carrier boundary. -/
def Executor.pushInjectRaw (e : Executor α cap) (x : α) : BaseIO Unit :=
  e.pushItems [x]

/-- Pop one item off the front of the shared list. -/
def Executor.popInject (e : Executor α cap) : IO (Option α) :=
  e.inject.atomically do
    let st ← get
    let r := st.items.pop
    match r.1 with
    | some x => set { st with items := r.2, served := st.served + 1 }; return (some x)
    | none   => set st; return none

/-- **Record that the driver's program has produced its value**, and wake every waiter, in the shared cell's
own section. Called by a driver's completion, which may be running on a carrier. -/
def Executor.noteFinished (e : Executor α cap) : IO Unit :=
  e.inject.atomically do
    let st ← get
    set { st with finished := true }
    e.cv.notifyAll

/-- Clear the driver's stop condition before a run starts. One driver per executor, so one flag, and a second
run on the same executor must not inherit the first one's. -/
def Executor.clearFinished (e : Executor α cap) : IO Unit :=
  e.inject.atomically do
    let st ← get
    set { st with finished := false }

/-- Is the executor stopping? A reading of the one flag every park and every loop exit reads. -/
def Executor.isStopping (e : Executor α cap) : IO Bool :=
  e.inject.atomically do return (← get).stopping

/-- Shutdown: the flag is set under the shared lock, so a park either sees it or is refused, and every
parked carrier is woken. -/
def Executor.stop (e : Executor α cap) : IO Unit :=
  e.inject.atomically do
    let st ← get
    set { st with stopping := true }
    e.cv.notifyAll

/-! ### A worker's own queue -/

/-- **T3, the local submit**: worker `i`'s ring, and the placement rule's overflow appended to the shared
list in the same path. The shared section is taken after this pool's, which is the only lock order here.

The push is owner-made — a step's own re-enqueue takes the route of the worker firing it — so it owes no wake
and takes no second section; the overflow, if any, unparks through `pushItems` as every shared push does.

`@[inline]`: a per-item hot path, like `takeFor` — the body is one pool transaction. -/
@[inline]
def Executor.submitLocalRaw (e : Executor α cap) (i : Nat) (x : α) : BaseIO Unit :=
  (e.cell i).atomically do
    let p ← get
    set e.poolPlaceholder
    let r := p.submit x
    set r.2
    if !r.1.isEmpty then e.pushItems r.1

/-- **T2, the local spawn**: worker `i`'s LIFO slot, displacing its occupant through the same placement
rule a submit uses. Owner-made, so no wake (see `submitLocalRaw`). -/
@[inline]
def Executor.spawnLocalRaw (e : Executor α cap) (i : Nat) (x : α) : BaseIO Unit :=
  (e.cell i).atomically do
    let p ← get
    set e.poolPlaceholder
    let r := p.spawn x
    set r.2
    if !r.1.isEmpty then e.pushItems r.1
/-- **T4, the tick**: worker `i`'s allowance refreshes, and only worker `i`'s. -/
def Executor.tickFor (e : Executor α cap) (i : Nat) : IO Unit :=
  (e.cell i).atomically do
    set (Pool.tick (← get))

/-- **T5, the steal**: one element out of one other worker's queue.

The thief takes **one** element — the victim's ring front — and the item *is* the take: it is returned to the
caller and nothing is staged in the thief's own queue. Batch size one is the design, and the reason is the lock
discipline D4 records: under a lock, batching lengthens the critical section and blocks the victim, so the
inversion is not worth the amortisation. The victim's **LIFO slot is never stolen**: `takeFromRing` cannot see
it, so the ring is the thief's only reach — which is also why a chain, whose links live in the slot, does not
cross carriers. -/
def Executor.stealInto (e : Executor α cap) (_i j : Nat) : IO (Option α) := do
  (e.cell j).atomically do
    let p ← get
    set e.poolPlaceholder
    let r := p.takeFromRing
    set r.2
    return r.1

/-- **T1 and S2: take one item for worker `i`.**

Worker `i`'s own queue first — the slot while the allowance lasts, else the slot cleared for the shared
list and then the ring — then one steal attempt against one other worker, round-robin, then the shared list.
The flush runs inside this pool's section and appends to the shared list there, which is the pool → inject
order again.

`@[inline]`: this is the per-item hot path, and the body's cost is all in its single pool transaction — a
call boundary here costs as much as the transaction, measured. -/
@[inline]
def Executor.takeFor (e : Executor α cap) (i : Nat) : IO (Option α) := do
  let item ← (e.cell i).atomically do
    let p ← get
    set e.poolPlaceholder
    -- The pool's decision carries the allowance's refresh: a take the slot served spends it, and any other
    -- decision — a flush, or a ring take — refreshes it, so the slot's *consecutive* polls are bounded at
    -- `lifoCap` while a chain that yields is never demoted. Folding the refresh into `takeReport` rather than
    -- ticking here is what makes this spelling and the driver's `takeReport` read one transaction, so the
    -- two cannot disagree about the allowance.
    let rep := p.takeReport
    set rep.pool
    if !rep.flushed.isEmpty then e.pushItems rep.flushed
    return rep.item
  match item with
  | some x => return some x
  | none =>
    if 1 < e.workers.size then
      match ← e.stealInto i ((i + 1) % e.workers.size) with
      | some x => return some x
      | none   => pure ()
    e.popInject

/-! ### Parking -/

/-- **S3, park worker `i`**: refused while its own queue or the shared list holds anything, recorded and
waited for otherwise.

The worker's own emptiness is read under its own lock first — only worker `i` writes that queue while it is
not running a step — and the inject's contents and the stopping flag are re-checked **inside** the shared
section that records the park and waits. That re-check is what a push cannot slip past: a push either happened
before this section and appears in the shared list, or happens after it and sees the park.

The park is recorded in the shared cell, which is what makes `parked` readable — and what a push tests before
it notifies. -/
def Executor.park (e : Executor α cap) (i : Nat) : IO Bool := do
  let empty ← (e.cell i).atomically do return (← get).inFlight == 0
  if !empty then return false
  else
    let recorded ← IO.mkRef false
    e.inject.atomicallyOnce e.cv
      (pred := do
        let st ← get
        if st.stopping ∨ st.items.size ≠ 0 then
          return true
        else
          -- Every waiter records itself, once per wait. The predicate is re-evaluated after every wake, and a
          -- spurious one must not carry the count past the threads that are actually parked.
          let already ← recorded.get
          if !already then
            set { st with parked := st.parked + 1 }
            recorded.set true
          return false)
      (k := do
        let st ← get
        if ← recorded.get then
          set { st with parked := if 0 < st.parked then st.parked - 1 else 0 }
          recorded.set false)
    return true

/-- **The driver's wait**: block until the shared list holds something or the program has finished.

It records the wait in the same `parked` field a carrier's park does, because the driver on the calling thread
*is* the waiter in its configuration — worker `0` is the thread that parks — and a producer's wake is decided
by that field. A wait that did not record itself is a wait nothing wakes: the shipped single-carrier driver
always counted itself (`Executor.parkUntilWork` set `sched.parked := 1` while waiting), and a second source of
truth for who waits is exactly what the protocol's one-cell design exists to avoid.

It does *not* treat `stopping` as a reason to proceed, because a stop is a drain and the driver is the thread
that keeps draining it: a continuation registered on a leaf is not in any queue, and abandoning the wait
abandons it. It does read `finished`, because the program's last step may run on a carrier while the driver
waits here. -/
def Executor.waitForWork (e : Executor α cap) : IO Unit := do
  let recorded ← IO.mkRef false
  e.inject.atomicallyOnce e.cv
    (pred := do
      let st ← get
      if st.items.size ≠ 0 ∨ st.finished then
        return true
      else
        -- Every waiter records itself, once per wait, the driver included: a wait that did not record itself
        -- is a wait nothing wakes, and a re-evaluated predicate must not count the same wait twice.
        let already ← recorded.get
        if !already then
          set { st with parked := st.parked + 1 }
          recorded.set true
        return false)
    (k := do
      let st ← get
      if ← recorded.get then
        set { st with parked := if 0 < st.parked then st.parked - 1 else 0 }
        recorded.set false)

/-- **The parallel entry's wait**: block the calling thread until the program records its completion.

The caller is not a carrier and does not run a worker loop, so it reads the completion flag the program's
last step sets (`noteFinished`). It polls rather than waiting on `e.cv`: a push wakes one waiter
(`notifyOne`), and a caller parked there competes with the carrier that wake is meant for. A caller's
predicate is only `finished`, so it would re-park and leave the carrier asleep. `noteFinished` still
`notifyAll`s the carriers' condition variable for any driver parked there. -/
def Executor.waitFinished (e : Executor α cap) : IO Unit := do
  -- **Not on the carriers' condition variable.** A push uses `notifyOne`, and a caller parked on `e.cv`
  -- competes with a carrier for that wake: the caller's predicate is only `finished`, so it re-parks and the
  -- carrier stays asleep. Poll the flag instead, leaving `e.cv` to the carriers (and the single-carrier
  -- driver) for which its one-wake accounting is written.
  let mut done := false
  while !done do
    done ← e.inject.atomically do return (← get).finished
    unless done do IO.sleep 1

/-! ### The carrier loop -/

/-- One more item fired on this carrier's books, and the clock it took. -/
def Executor.fireMetered (e : Executor α cap) (i : Nat) (fire : Nat → α → IO Unit) (x : α) : IO Unit := do
  if e.metered then
    let t0 ← IO.monoNanosNow
    fire i x
    let t1 ← IO.monoNanosNow
    e.counters.atomically do
      set (countersAt i (fun c => { c with fired := c.fired + 1, busyNanos := c.busyNanos + (t1 - t0) })
        (← get))
  else fire i x

/-- Record this carrier's thread id in its own counters entry, once, at the start of its shift. -/
def Executor.noteTid (e : Executor α cap) (i : Nat) : IO Unit := do
  let tid ← IO.getTID
  e.counters.atomically do
    set (countersAt i (fun c => { c with tid := tid }) (← get))

/-- **A carrier's shift.**

Take or park, until `stopping` is seen with nothing left to take; `fire` is the caller's, because what an item
is and how it runs belong to the layer above. A stop is a *drain*: the loop leaves when the flag is set **and**
this worker's own queue and the shared list are both empty, which is what `takeFor` returning `none` with
`stopping` set means.

There is deliberately **no** staged cut on this path. A cut on the wake half — the shared push's notify, this
predicate's re-check of the shared list, the take's consultation of it — reds the shipped single-carrier
contract as soon as one carrier is parked, so it would cost an existing scenario rather than stage a new one:
the staged reds this milestone measures are the parallel entry and the steal, and the parked count's
accounting. -/
def Executor.workerLoop (e : Executor α cap) (fire : Nat → α → IO Unit) (i : Nat) : IO Unit := do
  e.noteTid i
  let mut go := true
  while go do
    match ← e.takeFor i with
    | some x => e.fireMetered i fire x
    | none   =>
      if ← e.isStopping then go := false
      else let _ ← e.park i; pure ()

/-! ### The driver's operations: worker 0 on the calling thread -/

/-- **Submit into worker `0`'s queue**: the driver's spelling, with the calling thread standing in for
worker `0`. -/
@[expose] def Executor.submit (e : Executor α cap) (x : α) : IO Unit := do e.submitLocalRaw 0 x

/-- The `BaseIO` spelling a waker needs: enqueuing is the one thing a continuation registered on a stock
`Task` does, and a waker cannot call `IO`. -/
def Executor.submitBase (e : Executor α cap) (x : α) : BaseIO Unit := e.submitLocalRaw 0 x

/-- Submit into worker `i`'s queue, in `IO`. -/
def Executor.submitInto (e : Executor α cap) (i : Nat) (x : α) : IO Unit := do e.submitLocalRaw i x

/-- **Spawn on worker `0`**, owner-local: the item takes the slot. -/
def Executor.spawn (e : Executor α cap) (x : α) : IO Unit := do e.spawnLocalRaw 0 x

/-- The `BaseIO` spelling of the local spawn. -/
def Executor.spawnBase (e : Executor α cap) (x : α) : BaseIO Unit := e.spawnLocalRaw 0 x

/-- Spawn on worker `i`, in `IO`. -/
def Executor.spawnInto (e : Executor α cap) (i : Nat) (x : α) : IO Unit := do e.spawnLocalRaw i x

/-- **The driver's tick**: worker `0`'s allowance refreshes. -/
def Executor.tick (e : Executor α cap) : IO Unit := e.tickFor 0

/-- **A take for worker `0`, with the decision its record reads.**

The driver's take is the carrier's: the pool's own decision first (slot, flush, ring) and then the shared
list, so a `queue`-served item is whichever of the two held it. The record's `observed`/`served` come from
the pool's decision, which is the only place the allowance is observable. The decision carries the allowance's
refresh, so this spelling and the carrier's `takeFor` read one transaction and one bound. -/
def Executor.takeReport (e : Executor α cap) : IO (TakeReport α cap) := do
  let rep ← (e.cell 0).atomically do
    let p ← get
    set e.poolPlaceholder
    let rep := p.takeReport
    set rep.pool
    if !rep.flushed.isEmpty then e.pushItems rep.flushed
    return rep
  match rep.item with
  | some _ => return rep
  | none   =>
    match ← e.popInject with
    | some x => return { rep with item := some x }
    | none   => return rep

/-- Take one item of work: the decision without its report. -/
@[expose] def Executor.take (e : Executor α cap) : IO (Option α) := do
  return (← e.takeReport).item

/-- Wait for work and take one, or report that the executor is stopping with nothing left. -/
private def Executor.waitThenTake (e : Executor α cap) : IO (Option α) := do
  if ← e.isStopping then return none
  else
    e.waitForWork
    e.takeFor 0

/-- **One step of the driver**: take work, or wait until there is some. `idle` is asked once, and only when
the queues are empty while the executor still runs: it returns `true` when it produced work — a driver
advancing a virtual clock, whose fired timer enqueued a resumed step — so the second take finds it.

`none` means the executor is stopping with nothing left to take, which is the condition a serving loop exits
on; a wait that wakes for no item leaves the caller free to wait again. -/
def Executor.workWith (e : Executor α cap) (idle : IO Bool) : IO (Option α) := do
  match ← e.takeFor 0 with
  | some x => return some x
  | none   =>
    if ← idle then
      match ← e.takeFor 0 with
      | some x => return some x
      | none   => e.waitThenTake
    else e.waitThenTake

/-- One step of the driver with nowhere to advance to. -/
def Executor.work (e : Executor α cap) : IO (Option α) := e.workWith (do return false)

/-- **The whole composition as one reading**, for a client that needs more than the two counts: every
worker's pool under its own lock, the shared list, and the idle counters. -/
def Executor.snapshot (e : Executor α cap) : IO (Snapshot α cap) := do
  let mut ps : List (Pool α cap) := []
  for i in List.range e.workers.size do
    let p ← (e.cell i).atomically do return (← get)
    ps := ps ++ [p]
  let st ← e.inject.atomically do return (← get)
  return { workers := ps, inject := st.items.toList, injectServed := st.served,
           parked := st.parked, total := st.total, stopping := st.stopping }

/-- **What the executor currently holds and how many carriers are parked**: the composition's own two
numbers, read as one snapshot. -/
def Executor.observe (e : Executor α cap) : IO (Nat × Nat) := do
  let s ← e.snapshot
  return (s.held, s.parked)

/-- The per-carrier accumulators, read without mutating or notifying anything. -/
def Executor.metrics (e : Executor α cap) : IO (Option (List CarrierCounters)) := do
  if e.metered then
    let cs ← e.counters.atomically do return (← get)
    return some cs
  else return none

end LeanIn.Sched

end
