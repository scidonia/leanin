module

public import Std
public import Std.Http
public import LeanIn.Sched.Basic
public import LeanIn.Sched.Executor
public import LeanIn.Runtime.Basic
public import LeanIn.Http.Server
public import LeanIn.Runtime.Leaf
public import LeanIn.Runtime.Net
public import LeanIn.Runtime.Time
public import LeanIn.Runtime.Blocking
public import LeanIn.Test.Machines
public import LeanIn.Task.Sync
public import LeanIn.Task.Registry

public section

/-!
# Runtime controls for the bridge axioms

`LeanIn/Theory/Bridge.lean` asserts seven claims about the running `Std` primitives. An axiom nobody
checks is a liability, so each gets a control here — a test that distinguishes "the claim holds" from
"it does not".

Not all seven can be tested, and saying which is part of the point:

* **A1, A2, A5, A6, A7** are controlled below.
* **A3** (release requires ownership) cannot be *tested*, because violating it is undefined behaviour
  — the test would be the defect. It is discharged by reading `mutex.cpp` plus the standard, and the
  model expresses the constraint by having no transition for it.
* **A4** (spurious wakeups) cannot be *forced*: the implementation is permitted to wake spuriously, not
  obliged to. The control is therefore a tolerance test — a `waitUntil`-shaped loop must survive a
  wakeup it did not ask for — rather than an observation of one.
* **A6** (dedicated task ⇒ a new OS thread) is consumed by the blocking pool (D13) and is controlled
  below: a dedicated `Task` reads a value written before its spawn, reports a tid distinct from the
  caller's, and is `IO.wait`ed.
* The blocking pool's **promise-backed liveness witness** — `IO.Promise.new`/`resolve`/`result?` reached
  *directly* (D7's second primitive row, D13) — is controlled below too: `controlWitness` reads
  `IO.getTaskState` on the witness shape `spawnBlockingE` registers in `Hooks`.

Every control prints what it observed rather than only pass/fail, because A1 is a *race*: a lost update
is expected but not guaranteed on any given run, and a control that claimed otherwise would be lying.
-/

namespace LeanIn.Test

/-- **A2.** `tryLock` returns `false` on a held lock and `true` on a free one, and does not block
doing it.

The `tryLock` must come from a *different* thread than the holder: `std::mutex::try_lock` on a mutex
already locked by the calling thread is undefined behaviour, so the naive control would be the defect
it is meant to detect. -/
def controlTryLock : IO Unit := do
  let m ← Std.BaseMutex.new
  Std.BaseMutex.lock m
  let t₀ ← IO.monoNanosNow
  let held ← IO.asTask (do return (← Std.BaseMutex.tryLock m)) _root_.Task.Priority.dedicated
  let bHeld ← IO.wait held
  let t₁ ← IO.monoNanosNow
  Std.BaseMutex.unlock m
  let free ← IO.asTask (do return (← Std.BaseMutex.tryLock m)) _root_.Task.Priority.dedicated
  let bFree ← IO.wait free
  let heldOk := match bHeld with | .ok false => true | _ => false
  let freeOk := match bFree with | .ok true => true | _ => false
  IO.println s!"  A2  tryLock while held → false : {heldOk}"
  IO.println s!"  A2  tryLock while free → true  : {freeOk}"
  IO.println s!"  A2  the evidence for `true` is that it *returned* while the lock was held; the {t₁ - t₀} ns"
  IO.println s!"      it took is mostly the thread round-trip and proves nothing on its own"

/-- **A5.** A notification with no waiter is lost.

Issue `notifyOne` before anyone is waiting, then park a waiter and check — after a generous delay —
that it is still parked. Then `notifyAll` and check that it resumes. The first half is the claim; the
second half is the affirmative control, showing the machinery does wake a waiter when it is told to. -/
def controlNotifyLost (delayMs : UInt32) : IO Unit := do
  let m ← Std.BaseMutex.new
  let cv ← Std.Condvar.new
  Std.Condvar.notifyOne cv                    -- nobody is waiting: this one is lost
  let waiter ← IO.asTask (do
    Std.BaseMutex.lock m
    Std.Condvar.wait cv m
    Std.BaseMutex.unlock m) _root_.Task.Priority.dedicated
  IO.sleep delayMs
  let stillParked ← IO.getTaskState waiter
  Std.Condvar.notifyAll cv
  IO.sleep delayMs
  let resumed ← IO.getTaskState waiter
  IO.println s!"  A5  after a lost notify + {delayMs}ms, waiter is : {stillParked}"
  IO.println s!"      (`running` here means started-and-not-finished, i.e. still parked — a parked task"
  IO.println s!"       reports as `running` because its closure has been taken; see `object.cpp:1080`)"
  IO.println s!"  A5  after notifyAll + {delayMs}ms, waiter is        : {resumed}"

/-- **A7.** The monotone clock never goes backwards. -/
def controlClock (reads : Nat) : IO Unit := do
  let mut prev ← IO.monoNanosNow
  let mut regressions := 0
  let mut advances := 0
  for _ in List.range reads do
    let now ← IO.monoNanosNow
    if now < prev then regressions := regressions + 1
    if now > prev then advances := advances + 1
    prev := now
  IO.println s!"  A7  {reads} reads, {regressions} regressions, {advances} advances : monotone = {regressions == 0}"

/-- **A6.** A dedicated `Task` runs on a new OS thread, sees writes made before its spawn, and is joinable.

A value is written *before* the spawn, so seeing it in the task is the happens-before half of A6; the task's
tid differing from the caller's is "a new OS thread"; and `IO.wait` returning the task's result is the
joinable half. The pooling above the primitive — bounded *reuse* of such threads — is a different fact, read
at the work by SC12's off-carrier detector rather than here. -/
def controlDedicated : IO Unit := do
  let callerTid ← IO.getTID
  let before ← IO.mkRef (0 : Nat)
  before.set 42                                       -- written before the spawn
  let t ← IO.asTask (do
      let seen ← before.get
      let tid ← IO.getTID
      return (seen, tid)) _root_.Task.Priority.dedicated
  let r ← IO.wait t
  match r with
  | .ok (seen, tid) =>
    IO.println s!"  A6  caller tid={callerTid}  task tid={tid}  distinct = {callerTid != tid} (a new OS thread)"
    IO.println s!"  A6  value written before the spawn, read in the task : {seen} (happens-before = {seen == 42})"
    IO.println s!"  A6  IO.wait returned the task's result : joinable = true"
  | .error _ =>
    IO.println "  A6  the dedicated task failed"

/-- **The liveness witness.** `spawnBlockingE` registers a promise-backed stock `Task` in `Hooks`, built
with `IO.Promise.new`, `Promise.resolve` and `Promise.result?` reached *directly* (D7's second primitive
row, D13) — so those operations get a control here (the `A6` control above does not cover them).

The control reads `IO.getTaskState` on `(done.result?).map (fun _ => ()) (sync := true)`, the exact shape
`spawnBlockingE` registers (`LeanIn/Runtime/Blocking.lean:163-164`), at three points. Before `resolve` it
must not be `.finished`; after `resolve` it must be. The affirmative control is a *second* promise, never
resolved and kept live, whose witness stays not-`.finished` — so a reader stuck at either value is caught.
`waiting` and `running` are equivalent for promise-derived tasks (`Init/System/IO.lean:552-554`), so the
readings compare against `.finished` rather than a particular waiting state. The third reading is the
*dropped*-promise datum: a promise dropped without `resolve` settles its witness at `none`
(`Init/System/Promise.lean:29`). -/
def controlWitness : IO Unit := do
  let done ← IO.Promise.new (α := Unit)
  let witness := (done.result?).map (fun _ => ()) (sync := true)
  let before ← IO.getTaskState witness
  IO.println s!"  PW  witness before resolve : {before}  (not finished = {before != .finished})"
  done.resolve ()
  let after ← IO.getTaskState witness
  IO.println s!"  PW  witness after  resolve : {after}  (finished = {after == .finished})"
  -- Affirmative control: a promise never resolved stays not-`.finished` while it is kept live.
  -- `heldResolved` reads `held` *after* the state read, so the compiler cannot drop it before it.
  let held ← IO.Promise.new (α := Unit)
  let heldWitness := (held.result?).map (fun _ => ()) (sync := true)
  let heldState ← IO.getTaskState heldWitness
  let heldResolved ← IO.Promise.isResolved held
  IO.println s!"  PW  never-resolved, kept live : {heldState}  (not finished = {heldState != .finished}; resolved = {heldResolved})"
  -- The third reading: a promise dropped without `resolve` settles its witness at `none`.
  let droppedWitness : Task (Option Unit) ← (do
    let q ← IO.Promise.new (α := Unit)
    return q.result?)
  let droppedState ← IO.getTaskState droppedWitness
  let droppedValue ← IO.wait droppedWitness
  IO.println s!"  PW  dropped without resolve : {droppedState}  (finished = {droppedState == .finished}; value = {droppedValue})"

/-- **A1.** Mutual exclusion is load-bearing.

Four threads each increment a counter `iters` times. Unguarded, increments are lost to the race;
guarded, the total is exact.

The guarded half is the **affirmative control**: it shows the lock is doing the work, so the unguarded
loss is attributable to the missing lock rather than to the counter not existing. The unguarded half is
probabilistic — a race need not manifest — so the observed count is printed rather than asserted. -/
def controlMutualExclusion (threads iters : Nat) : IO (Nat × Nat) := do
  let r ← IO.mkRef (0 : Nat)
  let unguarded ← (List.range threads).mapM (fun _ => IO.asTask (do
      for _ in List.range iters do
        let v ← r.get
        r.set (v + 1)) _root_.Task.Priority.dedicated)
  for t in unguarded do let _ ← IO.wait t
  let raw ← r.get

  let m ← Std.Mutex.new (0 : Nat)
  let guarded ← (List.range threads).mapM (fun _ => IO.asTask (do
      for _ in List.range iters do
        m.atomically do set ((← get) + 1)) _root_.Task.Priority.dedicated)
  for t in guarded do let _ ← IO.wait t
  let exact ← m.atomically get

  let expected := threads * iters
  IO.println s!"  A1  {threads} threads x {iters} increments = {expected} expected"
  IO.println s!"  A1  unguarded → {raw}  ({if raw == expected then "no loss observed this run — a race need not manifest" else s!"{expected - raw} lost"})"
  IO.println s!"  A1  guarded   → {exact}  exact = {exact == expected}  (affirmative control)"
  return (raw, exact)

/-- **A4, as far as it can be controlled.** A wakeup that was never asked for must not corrupt a
`waitUntil`-shaped loop: the predicate is re-checked, so an unexpected resume just re-parks.

This does *not* observe a spurious wakeup — the implementation is permitted to wake spuriously, not
obliged to. It shows the shape the theory demands is the shape that tolerates one. -/
def controlPredicateRecheck (delayMs : UInt32) : IO Unit := do
  let m ← Std.BaseMutex.new
  let cv ← Std.Condvar.new
  let ready ← IO.mkRef false
  let waiter ← IO.asTask (do
    Std.BaseMutex.lock m
    Std.Condvar.waitUntil cv m (do return (← ready.get))
    Std.BaseMutex.unlock m) _root_.Task.Priority.dedicated
  IO.sleep delayMs
  Std.Condvar.notifyAll cv                    -- wakes it, but the predicate is still false
  IO.sleep delayMs
  let afterEmptyWake ← IO.getTaskState waiter
  ready.set true
  Std.Condvar.notifyAll cv
  IO.sleep delayMs
  let afterRealWake ← IO.getTaskState waiter
  IO.println s!"  A4  after a wake with the predicate false : {afterEmptyWake}  (re-parked = correct)"
  IO.println s!"  A4  after the predicate becomes true      : {afterRealWake}"

/-- **SC1 — the awaiter yields to a sibling on the invoking caller before the gated wake.**

One `blockOn` on the invoking thread. The awaited body and the sibling are both polled on that same
caller — the single-carrier claim — while the completion is a stock `Task` completing on a pool worker,
which is the *native* waker and must be a different thread. The gate is a mutex/condvar handshake
between the sibling and that completion, so the order is not decided by elapsed time.

The events are appended by the actor that caused them, where it occurred, and nothing retypes them from
a desired result: the awaiter appends `await-registered` on its first poll, the sibling appends its two,
and the completion's continuation appends the last when it resumes. -/
def executorSingle : IO UInt32 := do
  let q ← Sched.Queue.new
  let events ← IO.mkRef ([] : List String)
  let record (e : String) : IO Unit := events.modify (· ++ [e])
  let value ← IO.mkRef (0 : Nat)
  let callerTid ← IO.getTID
  let bodyTid ← IO.mkRef (0 : UInt64)
  let siblingTid ← IO.mkRef (0 : UInt64)
  let wakerTid ← IO.mkRef (0 : UInt64)
  let finished ← IO.mkRef false
  let gate ← Std.Mutex.new false
  let gateCv ← Std.Condvar.new
  -- The fake completion: a stock Task that blocks until the gate is released, then returns a value.
  let completion ← IO.asTask (do
    gate.atomicallyOnce gateCv (pred := do return (← get)) (k := do return ())
    return (7 : Nat)) _root_.Task.Priority.default
  -- What the completion's continuation enqueues when it fires: the awaited task's resume, not the
  -- body again. Hoisted out of the `BaseIO` continuation so its type is the job's, not that monad's.
  let resume : Sched.Job := do
    record "await-completed"
    finished.set true
    return true
  -- The hooked tasks live here: a continuation whose task is dropped is not a continuation.
  let hooks ← IO.mkRef ([] : List (Task Unit))
  -- The awaited body: polled on the caller. It registers its continuation once and parks.
  let awaited : Sched.Job := do
    if (← bodyTid.get) == 0 then bodyTid.set (← IO.getTID)
    record "await-registered"
    -- `IO.asTask` reports through the task's own result, so the continuation receives the `Except`.
    let hooked ← BaseIO.bindTask completion (fun r => do
      wakerTid.set (← IO.getTID)
      match r with
      | .ok v    => value.set v
      | .error _ => pure ()
      -- Inlined rather than `q.push`, whose type is `IO`: the continuation's monad is `BaseIO`.
      -- Same discipline either way -- append and notify under the one lock.
      q.lock.atomically do
        set ((← get) ++ [resume])
        q.cv.notifyOne
      return _root_.Task.pure ())
    hooks.modify (· ++ [hooked])
    return false
  -- The sibling: polled on the caller too, and it releases the gate the completion waits on.
  let sibling : Sched.Job := do
    if (← siblingTid.get) == 0 then siblingTid.set (← IO.getTID)
    record "sibling-done"
    gate.atomically do set true; gateCv.notifyAll
    record "gate-released"
    return true
  q.push awaited
  q.push sibling
  Sched.blockOn q (do return (← finished.get))
  let order ← events.get
  let v ← value.get
  IO.println s!"exec|single|caller={callerTid}|body={← bodyTid.get}|sibling={← siblingTid.get}|waker={← wakerTid.get}|result={v}|order={String.intercalate "," order}"
  return 0

/-- **SC3 — the executor's operation records against the pure model's.**

The script is `tests/ModelOracle.lean`'s, repeated here because that oracle is a fixture outside the library
and cannot be imported; the fixture checks that both sides produce the same number of records, and it is
nine. Each outcome is *computed* from the executor's own state after the transaction, exactly as the oracle's
is computed from the model's — neither side types an expected answer, so a match is evidence about the
executor rather than agreement between two copies of a fixture.

`take` advances the pool and the scheduler together or neither, and the record says which: a task with
`taken<n>`, or `-` with `none`. -/
inductive TraceOp where
  | submit (task : Nat)
  | enqueue (task : Nat)
  | take
  | park

/-- The fixed script, position 0 to 8. -/
def traceScript : List TraceOp :=
  [.submit 0, .submit 1, .park, .take, .take, .park, .enqueue 2, .take, .take]

/-- **A carrier-side park, observed from the state while it waits.**

`Executor.park` is the operation a carrier runs, and it records the park in the shared cell and then waits
there — so the count reads one *only* while the wait is pending. Driving it in process therefore cannot
produce the record at all: the value has to be read from the state at the moment the park is in progress. So
the park is driven on a dedicated thread and the state is polled in a bounded round loop (a round count, never
a clock), which is the staging SC2's parked-first order already used for `Executor.work`.

The thread parks again whenever a park returns without the cell recording one, which is what a pending local
push does — this mode's own `submit`s leave one behind — so the park that is observed at `parked = 1` is one
whose predecessor the cell demonstrably consumed, rather than a guessed iteration. The thread is returned
rather than joined here: the work that wakes it is produced afterwards, and the caller joins it before the
mode returns. -/
private def stagePark {cap : Nat} (e : Sched.Executor Nat cap) :
    IO (_root_.Task (Except IO.Error Unit) × Option Nat) := do
  let go ← IO.mkRef true
  let w ← IO.asTask (do
    while (← go.get) do
      let _ ← e.park 0
      pure ()) _root_.Task.Priority.dedicated
  let mut parked := 0
  let mut rounds := 0
  while parked == 0 && rounds < 1000 do
    IO.sleep 1
    parked := (← e.snapshot).parked
    rounds := rounds + 1
  go.set false
  return (w, if parked == 0 then none else some parked)

/-- Join the staged carrier-side threads. Called before the mode returns whatever the readings were, so no
thread of this mode's staging outlives the invocation. -/
private def joinStaged (pending : IO.Ref (List (_root_.Task (Except IO.Error Unit)))) : IO Unit := do
  for t in (← pending.get) do
    match ← IO.wait t with
    | .ok _    => pure ()
    | .error _ => pure ()

/-- A park the state never recorded inside the round bound is a defect of this mode rather than a `parked = 0`
reading, and the two are not the same failure: the executor is stopped so every staged thread can be joined,
and the invocation fails loudly instead of printing a count the park never produced. -/
private def setupParkFailure {cap : Nat} (e : Sched.Executor Nat cap)
    (pending : IO.Ref (List (_root_.Task (Except IO.Error Unit)))) : IO Unit := do
  e.stop
  joinStaged pending
  throw (IO.userError "controls: the state never recorded the park a staged carrier-side thread was driven to")

/-- **SC3's trace:** the fixed script, one record per step, each computed from the executor's own state.

Every position is a call this thread makes — the external delivery included, on worker 0's own queue — so no
position's outcome depends on which thread wins and no carrier is started. The one exception is a **granted**
park: `Executor.park` records itself in the shared cell and waits there, so its count is read from the state
while the wait is pending, driven on its own thread (`stagePark`) and drained by the stop before that thread is
joined. The fields a reader compares are unchanged. -/
def executorTrace : IO UInt32 := do
  let e ← Sched.Executor.new Nat 256 1
  let parks ← IO.mkRef ([] : List (_root_.Task (Except IO.Error Unit)))
  let mut pos : Nat := 0
  for o in traceScript do
    match o with
    | .submit t =>
      e.submit t
      let st ← e.snapshot
      IO.println s!"exec|trace|op=submit|pos={pos}|task={t}|out=inflight{st.held}"
    | .enqueue t =>
      -- The external delivery the way this scripted trace plays it: a call this thread makes on worker 0's own
      -- queue, with the same count as a submit. It is deliberately **not** the shared route: the shared route
      -- wakes a parked worker, and a park is pending at position 5, so the woken thread and this thread would
      -- race for the one item — the trace's outcome would then depend on which thread won.
      e.submit t
      let st ← e.snapshot
      IO.println s!"exec|trace|op=enqueue|pos={pos}|task={t}|out=inflight{st.held}"
    | .take =>
      let got ← e.take
      let st ← e.snapshot
      match got with
      | some x => IO.println s!"exec|trace|op=take|pos={pos}|task={x}|out=taken{st.taken}"
      | none   => IO.println s!"exec|trace|op=take|pos={pos}|task=-|out=none"
    | .park =>
      if (← e.snapshot).held ≠ 0 then
        -- Work is held, so the park is refused and answered at once rather than waited on.
        let _ ← e.park 0
        IO.println s!"exec|trace|op=park|pos={pos}|task=-|out=none"
      else
        -- Nothing is held, so the park is granted: `Executor.park` records itself in the shared cell and
        -- waits there, so it is driven on its own thread and the count is read from the state while the
        -- wait is pending — a value this thread observed, not one it assumed.
        let (w, seen) ← stagePark e
        parks.modify (· ++ [w])
        match seen with
        | some parked => IO.println s!"exec|trace|op=park|pos={pos}|task=-|out=parked{parked}"
        | none        => setupParkFailure e parks
    pos := pos + 1
  -- The park at position 5 recorded itself and waits; the delivery is a call this thread made on the local
  -- route and owes it no wake, so the wait is ended by the stop and the staging thread is then joined. No
  -- carrier is started by this mode.
  e.stop
  joinStaged parks
  return 0

/-- **SC2 — an injected completion wakes a waiting carrier, and shutdown delivers the staged work once.**

Two event orders, and neither is decided by elapsed time. In the *notification-first* order the producer
submits before any carrier exists, so a carrier started afterwards finds the work rather than parking. In the
*parked-first* order the carrier is started first, the harness waits until the state *says* it is parked, and
only then does the producer act — which is the order a naive protocol hangs on, since a notification with no
waiter is lost.

Then the shutdown half: two identities staged at the public `submit`, shutdown, and a carrier-side thread
that takes until the executor is stopping with nothing left. `delivered` is what it actually took, so a drain
that reported a zero count while completing nothing could not pass as one that delivered both.

`before` and `after` are the pending work completing in each order; each must be exactly one. The events are
appended where they happen, in the order they happened, and nothing retypes them from a desired result. -/
def executorPark (cap : Nat) : IO UInt32 := do
  let events ← IO.mkRef ([] : List String)
  let record (e : String) : IO Unit := events.modify (· ++ [e])

  -- Order 1: notification before any carrier parks.
  let e1 ← Sched.Executor.new Nat cap 1
  e1.submit 7
  record "pre-notify=emitted-before-park"
  let got1 ← IO.mkRef false
  let w1 ← IO.asTask (do
    match ← e1.work with
    | some _ => got1.set true
    | none   => pure ()) _root_.Task.Priority.dedicated
  match ← IO.wait w1 with
  | .ok _    => if ← got1.get then record "pre-notify=completed"
  | .error e => IO.println s!"executor-park: order 1 errored: {e}"

  -- Order 2: the carrier parked first, confirmed from the state before the producer acts.
  let e2 ← Sched.Executor.new Nat cap 1
  let got2 ← IO.mkRef false
  -- The carrier starts *first*: `Executor.park` is the carrier-side operation, and it records the park in
  -- the shared cell and waits there, so the state is read while the wait is pending — and the producer acts
  -- only once the state says the park has happened, which is what makes this the order a naive protocol
  -- hangs on: a notification with no waiter is lost.
  let (w2, parked2) ← stagePark e2
  match parked2 with
  | some _ => record "parked-first=parked"
  | none   => setupParkFailure e2 (← IO.mkRef [w2])
  -- A producer that is not the parked carrier takes the **shared** route: a local push into a worker's own
  -- queue is the owner's alone (the owner is running the step that makes it), so the foreign producer here is
  -- the shape the shared inject exists for. The assertion is unchanged — a notification with no waiter is lost.
  e2.pushInjectRaw 7
  record "producer=emitted-after-park"
  match ← IO.wait w2 with
  | .ok _    => got2.set true; record "parked-first=completed"
  | .error e => IO.println s!"executor-park: order 2 errored: {e}"

  -- Shutdown: stage two identities, stop, and let a carrier drain them. The drain takes through the same
  -- operation a carrier takes with and ends when the executor is stopping with nothing left, so it neither
  -- waits on a notification that a stop would not deliver nor reads a clock.
  let e3 ← Sched.Executor.new Nat cap 1
  let seen ← IO.mkRef ([] : List Nat)
  let carrier ← IO.asTask (do
    let mut go := true
    while go do
      match ← e3.takeFor 0 with
      | some x => seen.modify (· ++ [x])
      | none   => if ← e3.isStopping then go := false else IO.sleep 1) _root_.Task.Priority.dedicated
  let queued : List Nat := [31, 32]
  for t in queued do e3.submit t
  e3.stop
  match ← IO.wait carrier with
  | .error e => IO.println s!"executor-park: the carrier errored: {e}"
  | .ok _    => pure ()
  let delivered ← seen.get
  let st ← e3.snapshot
  if delivered.isEmpty then record "drain=1" else record "drain=0"

  let before := if ← got1.get then 1 else 0
  let after := if ← got2.get then 1 else 0
  IO.println s!"exec|park|before={before}|after={after}|observed={String.intercalate "," (← events.get)}|queued=[{String.intercalate "," (queued.map toString)}]|delivered=[{String.intercalate "," (delivered.map toString)}]|remaining={st.held}"
  return 0

/-- The value of a `--key=value` argument, for the modes that take one. -/
def argValue (args : List String) (key : String) : Option String :=
  args.findSome? fun a =>
    if a.startsWith (key ++ "=") then some ((a.drop (key.length + 1)).toString) else none

/-- The value of a space-separated `--key value` argument, the form a mode driven by a shell fixture
takes. -/
def argAfter : List String → String → Option String
  | k :: v :: rest, key => if k == key then some v else argAfter (v :: rest) key
  | _, _ => none

/-- A numeric argument, in either spelling a mode accepts (`--key=4` and `--key 4`), or the default. -/
def argNat (args : List String) (key : String) (default : Nat) : Nat :=
  match argValue args key with
  | some v => (String.toNat? v).getD default
  | none   => ((argAfter args key).bind String.toNat?).getD default


/-- The best of `k` runs of `x`, in microseconds. Best rather than mean: the thing being measured is the
runtime's own cost, and a mean would mostly report what the rest of the machine was doing. -/
def bestMicros (k : Nat) (x : IO Unit) : IO Nat := do
  let mut best := 0
  for _ in List.range k do
    let t0 ← IO.monoNanosNow
    x
    let t1 ← IO.monoNanosNow
    if best == 0 || t1 - t0 < best then best := t1 - t0
  return best / 1000

/-- **The runtime against the stock pool, on the two shapes the plan measures.**

`spike` measures Lean's scheduler; this measures ours on the same work. The work unit is the same on both
sides — one `Std.Mutex`-guarded increment — so the difference is the scheduler and not the payload.

The second shape is the one the plan's M4 exists for: four tasks that each sleep. Both sides overlap them now —
the stock pool on its eight workers, and this runtime by routing each sleep through the blocking pool
(`Runtime.spawnBlocking`), off the single carrier. Before the pool existed the `leanin` half serialised on the
carrier and read ≈4× the stock row; the number printed now is the pool's, and the row is its own record that the
defect is gone.

Not part of the library: a diagnostic, run as `lake exe controls --runtime-bench`. -/
def runtimeBench : IO UInt32 := do
  let n := 10000
  let blockers := 4
  let d : UInt32 := 25
  let k := 5
  IO.println s!"runtime bench: {n} tasks, {blockers} x {d}ms sleep, best of {k}"

  -- Shape 1: `n` independent units of work, each taking the same mutex once, spawned and then joined. The
  -- baseline is Lean's native `Task` at default priority -- a C++ task object pushed to the runtime's worker
  -- pool and joined with `lean_io_wait` -- which is the fastest unit of scheduled work Lean has, and not the
  -- same programming model as `Std.Async` or this runtime: its body runs to completion, it cannot yield.
  let stockTiny ← bestMicros k do
    let m ← Std.Mutex.new (0 : Nat)
    let ts ← (List.range n).mapM (fun _ =>
      IO.asTask (m.atomically do set ((← get) + 1)) _root_.Task.Priority.default)
    for t in ts do let _ ← IO.wait t
    pure ()
  let oursTiny ← bestMicros k do
    let m ← Std.Mutex.new (0 : Nat)
    let e ← Sched.Executor.new LeanIn.Task.Item 256 1
    let body : LeanIn.Task.Async Unit := LeanIn.Task.Async.ofIO (m.atomically do set ((← get) + 1))
    let _ ← Runtime.run e (do
      let hs ← (List.range n).mapM (fun _ => LeanIn.Task.Async.spawn body)
      for h in hs do let _ ← LeanIn.Task.Async.await h
      pure ())
    pure ()
  IO.println s!"{n} tasks, spawn+join   : native Task (default prio) {stockTiny}us / leanin {oursTiny}us"
  -- The native *green* baseline: `Async.block` drives Lean's async runtime on this thread, and `async`/`await`
  -- are its task, so this is the closest analogue of the runtime above rather than of the pool.
  let stockGreen ← bestMicros k do
    let m ← Std.Mutex.new (0 : Nat)
    Std.Async.Async.block do
      let hs ← (List.range n).mapM (fun _ =>
        Std.Async.async (m.atomically do set ((← get) + 1)))
      for h in hs do let _ ← Std.Async.await h
      pure ()
  IO.println s!"{n} tasks, spawn+join   : Std.Async {stockGreen}us"


  -- Shape 2: blocking work. Each task sleeps, which on one carrier stops everything.
  let stockSleep ← bestMicros k do
    let ts ← (List.range blockers).mapM (fun _ =>
      IO.asTask (IO.sleep d) _root_.Task.Priority.default)
    for t in ts do let _ ← IO.wait t
    pure ()
  let oursSleep ← bestMicros k do
    let e ← Sched.Executor.new LeanIn.Task.Item 256 1
    let hooks ← Runtime.Hooks.new
    let pool ← Runtime.BlockingPool.new blockers
    let _ ← Runtime.run e (do
      let hs ← (List.range blockers).mapM (fun _ =>
        LeanIn.Task.Async.spawn (Runtime.spawnBlocking pool hooks (IO.sleep d)))
      for h in hs do let _ ← LeanIn.Task.Async.await h
      pure ())
    Runtime.BlockingPool.shutdownAndWait pool
    pure ()
  IO.println s!"{blockers} x {d}ms sleeps      : stock {stockSleep}us / leanin {oursSleep}us"

  -- Where our code actually ran, which is the other half of any throughput number.
  let e ← Sched.Executor.new LeanIn.Task.Item 256 1
  let tids ← IO.mkRef ([] : List UInt64)
  let body : LeanIn.Task.Async Unit := LeanIn.Task.Async.ofIO do
    tids.modify (· ++ [← IO.getTID])
  let _ ← Runtime.run e (do
    let hs ← (List.range 64).mapM (fun _ => LeanIn.Task.Async.spawn body)
    for h in hs do let _ ← LeanIn.Task.Async.await h
    pure ())
  let distinct := (← tids.get).foldl (fun acc t => if acc.contains t then acc else acc ++ [t]) []
  IO.println s!"64 spawned tasks       : {distinct.length} distinct threads"
  return 0

/-- **Where a work item can be delayed, and by how much.** Three shapes, each measured rather than argued:

* `tail` — the same O(1) payload on both sides, so the number is the *scheduler's* and not the payload's: how
  long after the first task does the last of them start.
* `queue` — `W` workers occupied by blocking work, then `W` more tasks that want a worker. This is the pool's
  starvation shape: with no spare worker, ready work does not run at all, for as long as the occupiers hold on.
* `blockqueue` — the same workload with the blockers routed through this runtime's blocking pool: `W` pool jobs
  of 300ms and `W` further items queued behind them, at a pool width printed on the line. At `W` workers the
  further items finish about a blocker later; the same line at one worker is the control that it reads the
  pool's width rather than a fixed quantity.
* `dedicated` — one OS thread per task, which is what "more threads than workers" means when the priority asks
  for it. `LEAN_NUM_THREADS` does not affect this one.

Diagnostic, not part of the library: `lake exe controls --runtime-tail`. -/
def runtimeTail : IO UInt32 := do
  let n := 10000
  -- (1) How far behind can a work item get? Every task records when it *started*; the last start is the tail.
  let m ← Std.Mutex.new (0 : Nat)
  let t0 ← IO.monoNanosNow
  let ts ← (List.range n).mapM (fun _ => IO.asTask (do
    let t ← IO.monoNanosNow
    m.atomically do set (max (← get) (t - t0))) _root_.Task.Priority.default)
  for t in ts do let _ ← IO.wait t
  let poolLast ← m.atomically get
  IO.println s!"tail    : pool, last of {n} tasks started {poolLast / 1000}us after the first"

  let e ← Sched.Executor.new LeanIn.Task.Item 256 1
  let m2 ← Std.Mutex.new (0 : Nat)
  let t1 ← IO.monoNanosNow
  let body : LeanIn.Task.Async Unit := LeanIn.Task.Async.ofIO do
    let t ← IO.monoNanosNow
    m2.atomically do set (max (← get) (t - t1))
  let _ ← Runtime.run e (do
    let hs ← (List.range n).mapM (fun _ => LeanIn.Task.Async.spawn body)
    for h in hs do let _ ← LeanIn.Task.Async.await h
    pure ())
  let t2 ← IO.monoNanosNow
  let oursLast ← m2.atomically get
  IO.println s!"tail    : leanin, last of {n} tasks started {oursLast / 1000}us after the first, run {(t2 - t1) / 1000}us"

  -- (2) Queued behind blocking work: W workers occupied for 300ms, then W more tasks want a worker.
  let w : Nat := 8
  let t3 ← IO.monoNanosNow
  let blockers ← (List.range w).mapM (fun _ => IO.asTask (IO.sleep 300) _root_.Task.Priority.default)
  IO.sleep 100
  let after ← (List.range w).mapM (fun _ => IO.asTask (return ()) _root_.Task.Priority.default)
  for t in after do let _ ← IO.wait t
  let t4 ← IO.monoNanosNow
  IO.println s!"queue   : {w} workers blocked 300ms; {w} further tasks finished at {(t4 - t3) / 1000}us"
  for t in blockers do let _ ← IO.wait t

  -- (2b) The same 8 × 300ms workload with the blockers in the runtime's blocking pool. `w` jobs occupy the
  -- pool's workers and `w` further items queue behind them; the pool's width is the line's own configuration,
  -- so the reading is compared against the width printed beside it and not across a `LEAN_NUM_THREADS` setting.
  -- At `w` workers the further items finish about a blocker later; at one worker the blockers serialise again,
  -- which is the control that the line measures the pool's width rather than a fixed quantity.
  let blockQueue (width : Nat) : IO Unit := do
    let hooks ← Runtime.Hooks.new
    let be ← Sched.Executor.new LeanIn.Task.Item 256 1
    let pool ← Runtime.BlockingPool.new width
    let b0 ← IO.monoNanosNow
    let _ ← Runtime.run be (do
      let bjobs ← (List.range w).mapM (fun _ =>
        LeanIn.Task.Async.spawn (Runtime.spawnBlocking pool hooks (IO.sleep 300)))
      let bmore ← (List.range w).mapM (fun _ =>
        LeanIn.Task.Async.spawn (Runtime.spawnBlocking pool hooks (pure () : IO Unit)))
      for h in bmore do let _ ← LeanIn.Task.Async.await h
      for h in bjobs do let _ ← LeanIn.Task.Async.await h
      pure ())
    let b1 ← IO.monoNanosNow
    Runtime.BlockingPool.shutdownAndWait pool
    IO.println s!"blockqueue : {w} pool jobs of 300ms on {width} workers; last finished at {(b1 - b0) / 1000}us"
  blockQueue w
  blockQueue 1

  -- (3) Ten thousand dedicated tasks: one OS thread each.
  let t5 ← IO.monoNanosNow
  let many ← (List.range 10000).mapM (fun _ => IO.asTask (return ()) _root_.Task.Priority.dedicated)
  for t in many do let _ ← IO.wait t
  let t6 ← IO.monoNanosNow
  IO.println s!"dedicat : 10000 dedicated tasks, one thread each, ran in {(t6 - t5) / 1000}us"
  return 0

/-- **Shared mutable state, and what each design has to pay for it.**

Three measurements, because the interesting question is not "who is faster" but "what does the *same* shared
state cost under each discipline":

* Each side runs the same counter with the strongest discipline its design *requires*: the pool's tasks run on
  eight threads, so it must hold a mutex; this runtime has one carrier, so a plain `IO.Ref` is already correct
  and it pays nothing. The final count is printed on both sides, so a lost update would be visible rather than
  assumed away — and a third measurement shows why the pool cannot drop its lock: a wider window (fewer tasks,
  more increments each) loses updates without it.
Not measured here, and deliberately: a task that holds a blocking lock across a yield wedges the carrier, so
demonstrating it means hanging a process. It is structural rather than empirical — the second task's `lock`
cannot return, because the only thread that could release it is inside that call — and it belongs in a
scenario with a watchdog, not in a diagnostic.

Diagnostic: `lake exe controls --runtime-shared`. -/
def runtimeShared : IO UInt32 := do
  let n := 10000
  -- The pool, with the lock its eight threads require.
  let t0 ← IO.monoNanosNow
  let m ← Std.Mutex.new (0 : Nat)
  let ts ← (List.range n).mapM (fun _ => IO.asTask (m.atomically do set ((← get) + 1)) _root_.Task.Priority.default)
  for t in ts do let _ ← IO.wait t
  let poolCount ← m.atomically get
  let t1 ← IO.monoNanosNow
  -- This runtime, with nothing but a ref: one carrier, so there is nothing to guard against.
  let r ← IO.mkRef (0 : Nat)
  let e ← Sched.Executor.new LeanIn.Task.Item 256 1
  let body : LeanIn.Task.Async Unit := LeanIn.Task.Async.ofIO do r.set ((← r.get) + 1)
  let t2 ← IO.monoNanosNow
  let _ ← Runtime.run e (do
    let hs ← (List.range n).mapM (fun _ => LeanIn.Task.Async.spawn body)
    for h in hs do let _ ← LeanIn.Task.Async.await h
    pure ())
  let oursCount ← r.get
  let t3 ← IO.monoNanosNow
  IO.println s!"shared  : pool+mutex {(t1 - t0) / 1000}us count={poolCount} / leanin+ref {(t3 - t2) / 1000}us count={oursCount}"
  -- …and the control for the pool's lock: same shape, wider window, no lock.
  let wide := 200000
  let raw ← IO.mkRef (0 : Nat)
  let ts2 ← (List.range 4).mapM (fun _ => IO.asTask (do
    for _ in List.range wide do
      raw.set ((← raw.get) + 1)) _root_.Task.Priority.default)
  for t in ts2 do let _ ← IO.wait t
  let rawCount ← raw.get
  IO.println s!"shared  : pool WITHOUT its lock: {rawCount} of {4 * wide} (lost {4 * wide - rawCount}) — so the lock is not optional there"

  return 0

/-- Spawn a child and await it, `n` times, inside one driver run: the round-trip shape, with the driver's
setup outside the measurement. -/
def roundTripProgram (ticks : IO.Ref Nat) (n : Nat) : LeanIn.Task.Async Unit := do
  let rec go (m : Nat) : LeanIn.Task.Async Unit := do
    if m = 0 then pure ()
    else
      let h ← LeanIn.Task.Async.spawn (LeanIn.Task.Async.ofIO do ticks.modify (· + 1))
      let _ ← LeanIn.Task.Async.await h
      go (m - 1)
  go n

/-- The round-trip figure: one child spawned and awaited immediately, repeated, inside one driver run. The
`spawn+take` row above is the queue's throughput; this is what a dependent chain costs per link. -/
def roundTripMicros (k : Nat) : IO Nat := do
  let ticks ← IO.mkRef (0 : Nat)
  let e ← Sched.Executor.new LeanIn.Task.Item 256 1
  let t0 ← IO.monoNanosNow
  let _ ← Runtime.run e (roundTripProgram ticks k)
  let t1 ← IO.monoNanosNow
  return (t1 - t0) / k

/-- **What one operation costs.** The end-to-end benchmarks say we are slower; these say which operation is
paying for it, in nanoseconds, best of three.

Each row is one call, so a task's cost is the sum of the rows it uses: a spawn-and-join task takes one submit
or spawn, one `work` per step, usually an `await` (two cell locks) and a `resume`. The comparison rows are the
primitives Tokio-style designs do *not* pay: a mutex critical section, a condvar notification with nobody
parked, and a `Join` (whose own `Std.Mutex` is built with it).

The last row is the blocking pool's cost from the carrier, decomposed the way the cancellation rows are: the
submission alone and a spawn-and-await round trip through the runtime, each over `k` trivial jobs at a pool
width printed on the line, because the figure means nothing without the configuration it was taken at.

Diagnostic: `lake exe controls --runtime-ops`. -/
def runtimeOps : IO UInt32 := do
  let k := 20000
  let best (x : IO Unit) : IO Nat := do
    let mut b := 0
    for _ in List.range 2 do
      let t0 ← IO.monoNanosNow
      x
      let t1 ← IO.monoNanosNow
      if b == 0 || t1 - t0 < b then b := t1 - t0
    return b / k        -- b is nanoseconds, so this is ns per operation
  let r ← IO.mkRef (0 : Nat)
  let refNs ← best do for _ in List.range k do r.set ((← r.get) + 1)
  let m ← Std.Mutex.new (0 : Nat)
  let mutexNs ← best do for _ in List.range k do m.atomically do set ((← get) + 1)
  let cv ← Std.Condvar.new
  let notifyNs ← best do for _ in List.range k do cv.notifyOne
  let joinNs ← best do for _ in List.range k do let _ ← LeanIn.Task.Join.new (α := Unit)
  -- What the "pool" baseline in the benchmark measures, one unit of it: a native `Task` with a trivial body,
  -- spawned at default priority and joined.
  let nativeNs ← best do for _ in List.range k do
    let t ← IO.asTask (pure ()) _root_.Task.Priority.default
    let _ ← IO.wait t
  -- The same round trip for this runtime: the latency figure, whose counterpart is the native row above.
  let roundNs ← roundTripMicros k
  -- The overflow path in isolation: `Ring.keepFirst` then `push` on a full ring, which is what the overflow
  -- does once per ~128 enqueues. The kept half's slots are neither read nor rewritten — the live count moves —
  -- so this is the cost of one overflow event.
  let mut full : LeanIn.Ring Nat 256 := LeanIn.emptyRing Nat 256
  for i in List.range 256 do full := full.push i
  let overflowNs ← best do for _ in List.range k do
    let r := (full.keepFirst (256 / 2)).push 0
    if r.size ≠ 256 / 2 + 1 then IO.println "overflow kept the wrong count"
  let e ← Sched.Executor.new LeanIn.Task.Item 256 1
  let item : LeanIn.Task.Item := LeanIn.Task.Item.ofAction (pure ())
  let spawnNs ← best do for _ in List.range k do e.spawn item
  let e2 ← Sched.Executor.new LeanIn.Task.Item 256 1
  let submitNs ← best do for _ in List.range k do e2.submit item
  let e3 ← Sched.Executor.new LeanIn.Task.Item 256 1
  for _ in List.range k do e3.submit item
  let workNs ← best do for _ in List.range k do let _ ← e3.takeFor 0
  -- The steady state the benchmarks run in: enqueue a step and consume it, so the ring never saturates.
  -- The rows above measure a *burst* -- 20 000 items through a 256-slot ring -- which is a different cost.
  let e4 ← Sched.Executor.new LeanIn.Task.Item 256 1
  let steadyNs ← best do for _ in List.range k do
    e4.spawn item
    let _ ← e4.takeFor 0
  -- The blocking pool's cost from the carrier, decomposed the way the cancellation rows are. `submit` is the
  -- submission *alone*, with the queue kept short by awaiting each job before the next submit — a tight submit
  -- loop would starve the workers and measure the queue's growing `List` append rather than the call. The
  -- round trip is the same job spawned and awaited through the runtime, which is what the carrier actually
  -- pays. The configuration is on the printed line, so the row cannot be read without the job count and pool
  -- width it was taken at. Best of two, like the rows beside it.
  let pw := 4
  let poolBench : IO (Nat × Nat) := do
    let p ← Runtime.BlockingPool.new pw
    let mut subNs := 0
    for _ in List.range k do
      let pr ← IO.Promise.new (α := Unit)
      let s0 ← IO.monoNanosNow
      Runtime.BlockingPool.submit p (pr.resolve ())
      let s1 ← IO.monoNanosNow
      subNs := subNs + (s1 - s0)
      let _ ← IO.wait (pr.result?.map (fun _ => ()) (sync := true))
    Runtime.BlockingPool.shutdownAndWait p
    let hooks ← Runtime.Hooks.new
    let pe ← Sched.Executor.new LeanIn.Task.Item 256 1
    let p2 ← Runtime.BlockingPool.new pw
    let rt0 ← IO.monoNanosNow
    let _ ← Runtime.run pe (do
      for _ in List.range k do
        let h ← LeanIn.Task.Async.spawn (Runtime.spawnBlocking p2 hooks (pure () : IO Unit))
        let _ ← LeanIn.Task.Async.await h
        pure ())
    let rt1 ← IO.monoNanosNow
    Runtime.BlockingPool.shutdownAndWait p2
    return (subNs / k, (rt1 - rt0) / k)
  let mut subPer := 0
  let mut rtPer := 0
  for _ in List.range 2 do
    let (s, r) ← poolBench
    if subPer == 0 || s < subPer then subPer := s
    if rtPer == 0 || r < rtPer then rtPer := r
  IO.println s!"ops: native Task spawn+join {nativeNs}ns | ref set/get {refNs}ns | mutex section {mutexNs}ns | notify (nobody parked) {notifyNs}ns"
  IO.println s!"ops: leanin Ring.keepFirst+push (full 256) {overflowNs}ns | leanin spawn+await round trip {roundNs}ns"
  IO.println s!"ops: Join.new {joinNs}ns | Executor.spawn {spawnNs}ns | Executor.submit {submitNs}ns | Executor.takeFor {workNs}ns | spawn+take (steady) {steadyNs}ns"
  IO.println s!"ops: blocking pool, {k} jobs on {pw} workers: submit {subPer}ns | spawn+await round trip {rtPer}ns per job ({rtPer / 1000}us)"
  return 0

/-- **The workload the `Std.Async` row is compared on, swept.** 10 000 units, each taking one mutex and
incrementing a counter, spawned and then joined -- the shape `--runtime-bench` measures against
`Std.Async.Async.block`.

Ours takes its worker count as an argument, so the row sweeps in-process. The stock pool's size is fixed when
the process starts, so its row sweeps by re-running the executable under `LEAN_NUM_THREADS`. The row with no
body separates the pool and the task machinery from the mutex the body takes.

Diagnostic: `lake exe controls --runtime-async`, and `LEAN_NUM_THREADS=n lake exe controls --runtime-async`. -/
def runtimeAsync : IO UInt32 := do
  let n := 10000
  let k := 5
  let ours (workers : Nat) (body : LeanIn.Task.Async Unit) : IO Nat := bestMicros k do
    let e ← Sched.Executor.new LeanIn.Task.Item 256 workers
    let _ ← Runtime.run e (do
      let hs ← (List.range n).mapM (fun _ => LeanIn.Task.Async.spawn body)
      for h in hs do let _ ← LeanIn.Task.Async.await h
      pure ())
    pure ()
  let m ← Std.Mutex.new (0 : Nat)
  let counting : LeanIn.Task.Async Unit := LeanIn.Task.Async.ofIO (m.atomically do set ((← get) + 1))
  for w in [1, 2, 4, 8] do
    let t ← ours w counting
    IO.println s!"async shape  {n} tasks  leanin {w} workers      : {t}us"
  let nop : LeanIn.Task.Async Unit := LeanIn.Task.Async.ofIO (pure ())
  for w in [1, 4] do
    let t ← ours w nop
    IO.println s!"async shape  {n} tasks  leanin {w} workers, no body: {t}us"
  let green ← bestMicros k do
    let m ← Std.Mutex.new (0 : Nat)
    Std.Async.Async.block do
      let hs ← (List.range n).mapM (fun _ => Std.Async.async (m.atomically do set ((← get) + 1)))
      for h in hs do let _ ← Std.Async.await h
      pure ()
  IO.println s!"async shape  {n} tasks  Std.Async                 : {green}us"
  return 0

/-- **Where one executor transaction's nanoseconds go.** A transaction is the lock, a copy of the state and
the scheduler; the pool's part of it is a ring mutation, and a ring mutation copies its array whenever the
array is still referenced somewhere else -- which is exactly what reading the state out of the mutex cell
leaves behind. Two ring rows settle that: `push` with the array uniquely held (the old ring is dead at the
call) against `push` with a live ring sharing it.

The `+ Pool.submit` row is the pool's own mutation now: the inject left `Pool` for the executor's shared cell,
so the append a burst walks is no longer inside this transaction, and the shared list's own cost is what the
`--runtime-carriers` rows are about.

Diagnostic: `lake exe controls --runtime-unit`. -/
def runtimeUnit : IO UInt32 := do
  let k := 20000
  let best (x : IO Unit) : IO Nat := do
    let mut b := 0
    for _ in List.range 2 do
      let t0 ← IO.monoNanosNow
      x
      let t1 ← IO.monoNanosNow
      if b == 0 || t1 - t0 < b then b := t1 - t0
    return b / k
  let item : LeanIn.Task.Item := LeanIn.Task.Item.ofAction (pure ())
  -- The transaction's own state: a worker's pool and the wake protocol beside it — the pair the executor's
  -- `State` used to name, written out here because that structure is gone and this row is about the cost of
  -- the transaction, not about the executor. `Pool.submit`/`spawn` return the overflow they did not keep, so
  -- the row takes the pool half of each result.
  let init : LeanIn.Sched.Pool LeanIn.Task.Item 256 × LeanIn.Sched.Scheduler :=
    (LeanIn.Sched.emptyPool LeanIn.Task.Item 256, LeanIn.Sched.Scheduler.initial 1)
  let m ← Std.Mutex.new init
  let plumb ← best do for _ in List.range k do
    m.atomically do let s ← get; set (s.1, s.2.enqueue)
  let withsub ← best do for _ in List.range k do
    m.atomically do
      let s ← get
      set ((s.1.submit item).2, s.2.enqueue)
  let withspawn ← best do for _ in List.range k do
    m.atomically do
      let s ← get
      set ((s.1.spawn item).2, s.2.enqueue)
  let uni ← best do
    let mut r : LeanIn.Ring Nat 256 := LeanIn.emptyRing Nat 256
    for i in List.range k do r := r.push i
    if r.size = 0 then IO.println "push did nothing"
  let sh ← best do
    let base : LeanIn.Ring Nat 256 := LeanIn.emptyRing Nat 256
    for i in List.range k do
      let r := base.push i
      if r.size = 0 then IO.println "push did nothing"
  IO.println s!"unit: transaction plumbing {plumb}ns | + Pool.submit {withsub}ns | + Pool.spawn {withspawn}ns"
  IO.println s!"unit: Ring.push unique array {uni}ns | array shared with a live ring {sh}ns"
  return 0

/-- Distinct elements, in order. The detector the thread-identity observations are read with, named so that its
own control below can call the same function rather than a lookalike. -/
private def distinctOf (xs : List UInt64) : List UInt64 :=
  xs.foldl (fun acc t => if acc.contains t then acc else acc ++ [t]) []

/-- The bytes a client read back, as one record field: `\`→`\\`, CR→`\r`, LF→`\n`, every other byte verbatim.
Named so the scenario's own literal can be written in exactly the escaping this prints. -/
private def escBytes (b : ByteArray) : String :=
  String.ofList <| b.toList.flatMap (fun c =>
    if c == 0x5C then ['\\', '\\']
    else if c == 0x0D then ['\\', 'r']
    else if c == 0x0A then ['\\', 'n']
    else [Char.ofNat c.toNat])

/-- **Echo an accepted connection until the peer stops, then shut it down.** The server-side peer of
`Runtime.echoConn`, which is the client's half: this one runs on a connection an accept loop produced, and its
socket operations are the runtime's own path rather than `Std.Async`'s. A socket failure ends the connection
rather than the mode, which is what the body of an accept loop wants: the peer going away mid-stream is an
ordinary event here.

`partial` for the same reason `Runtime.echoConn` is: a connection has no bound, and `Async` is `Inhabited`. -/
private partial def echoAccepted (hooks : Runtime.Hooks) (c : Runtime.Conn) :
    LeanIn.Task.EAsync IO.Error Unit := do
  try
    match ← Runtime.Conn.recv c hooks with
    | none    => Runtime.Conn.shutdown c hooks
    | some bs => Runtime.Conn.send c hooks bs; echoAccepted hooks c
  catch _ => pure ()

/-- **W2's evidence: sockets driven from our carriers.**

The server half is ours — bind, an accept loop of ours, one task per connection, all as `Task.Async` steps on
one executor driven by one thread. The client half is deliberately `Std.Async`'s, driven by `Async.block` on
this thread: a client that is not ours is what makes the thread identities mean anything.

One record line, in the shape the scenario fixtures read, and controls for the detectors in it, because an
absence detector that cannot report a presence proves nothing. The thread detector is shown counting two on a
two-distinct sample and one on a repeat. The reply comparison is shown against a payload with one extra byte,
where it must find nothing. And `heldBefore` is the same observer as `inFlightAfter`, read while three items
are deliberately queued and nothing is driving — `3` and then `0` is a reader that moves, where a first
attempt at this control read the pool from inside a running connection body and got `0`, which proves nothing:
a carrier drains the pool as it goes, so that reading is legitimately empty.

Diagnostic: `lake exe controls --runtime-net`. -/
def runtimeNet : IO UInt32 := do
  let n := 16
  let payload : ByteArray := "leanin over a socket".toUTF8
  let hooks ← Runtime.Hooks.new
  let l ← Runtime.Listener.bind (Runtime.loopback 0)
  let addr ← Runtime.Listener.sockName l
  let e ← Sched.Executor.new LeanIn.Task.Item 256 1
  let srvTids ← IO.mkRef ([] : List UInt64)
  let body : Runtime.Conn → LeanIn.Task.EAsync IO.Error Unit := fun c => do
    let tid ← monadLift (IO.getTID : IO UInt64)
    srvTids.modify (· ++ [tid])
    echoAccepted hooks c
  -- the control: the pool holds work only until a carrier takes it, so the reader is shown a queue nothing is
  -- draining. These three no-op items are taken first when the driver starts, and they change nothing else.
  for _ in List.range 3 do e.submit (LeanIn.Task.Item.ofAction (pure ()))
  let (heldBefore, _) ← e.observe
  let server ← IO.asTask (Runtime.run e (do
    srvTids.modify (· ++ [← IO.getTID])
    Runtime.serveNJoin hooks l n body)) _root_.Task.Priority.dedicated
  let clientTid ← IO.getTID
  let t0 ← IO.monoNanosNow
  let replies ← Std.Async.Async.block do
    let hs ← (List.range n).mapM (fun _ => Std.Async.async (do
      let c ← Std.Async.TCP.Socket.Client.mk
      c.connect addr
      c.send payload
      let got ← c.recv? 65536
      c.shutdown
      return got))
    hs.mapM (fun h => Std.Async.await h)
  let t1 ← IO.monoNanosNow
  let outcome ← IO.wait server
  let tids ← srvTids.get
  let distinct := distinctOf tids
  let exact := (replies.filter (fun r => r == some payload)).length
  let perturbed := (replies.filter (fun r => r == some (payload.push 0))).length
  -- An error-channel probe lived here: a refused connect to a dead port, and an accepted connect to this run's
  -- own listener as its affirmative control. It was removed rather than fixed in place because it makes the
  -- process die with SIGSEGV, and two things about it are worth keeping:
  --
  -- * A socket's descriptor closes when the Lean object owning it is collected. The first version read the
  --   listener's address early and probed later, and was refused by a socket it had just served sixteen
  --   connections on; reading the address in the same step as the probe fixed that, which is why the second
  --   version reached the accepted connect at all.
  -- * With the listener kept alive across the probe, the process then segfaults — during the run, not at the
  --   exit, and before the record is printed. The likely shape is a libuv handle finalised at a point the loop
  --   is no longer prepared for, but that is a hypothesis and not a finding: it needs isolating in its own mode
  --   before anything is built on it.
  --
  -- What is *not* in doubt is the library: `EAsync` is in and the socket layer returns failures rather than
  -- raising. `Runtime.connect` exists for the probe and for the driver's own tests.
  let (inFlightAfter, _) ← e.observe
  -- A shipped-path echo server for the same workload was tried here and backed out: an accept loop with a
  -- per-connection `background` does not elaborate inside this module (`whnf` heartbeat exhaustion in the
  -- shipped combinators). The comparison it was for is W16's item, where the server under the harness is a
  -- variable by design rather than a second copy of the loop living in a diagnostic.
  match outcome with
  | .error err => IO.println s!"net|failed={err}"; return 1
  | .ok (.error err) => IO.println s!"net|failed={err}"; return 1
  | .ok (.ok ()) =>
    IO.println s!"net|connections={n}|serverThreads={distinct.length}|clientAmongServer={distinct.contains clientTid}|echoes={exact}|heldBefore={heldBefore}|inFlightAfter={inFlightAfter}|wallUs={(t1 - t0) / 1000}"
    IO.println s!"netctl|threadsOnTwo={(distinctOf [0, 1]).length}|threadsOnRepeat={(distinctOf [7, 7]).length}|perturbed={perturbed}"
    return 0



/-- **W9's evidence: one HTTP request over a real loopback socket, byte-exactly, on our carrier.**

The listener is bound by this run (`Runtime.loopback 0`) and the connection is real; the client that sends the
one request line is `Std.Async`'s TCP client, driven by `Async.block` on this thread — a client that is not ours
is what makes the thread identities mean anything. The response bytes the client reads back are the observable,
printed escaped so the field stays one token (`\`→`\\`, CR→`\r`, LF→`\n`).

The per-connection half is `LeanIn.Http.Server.serveConn`, driven by `Runtime.serveNJoin` — the accept loop of ours —
so the socket bytes are carried through the `LeanIn.Http.H1` machine and the handler is dispatched
inline on the carrier the connection runs on. `Std.Http.Server`'s loop would have spawned it with `.asTask`
(`Std/Http/Server/Connection.lean:319`), putting it back on the stock pool — the observation SC19's carrier
clause reports.

One record line, in the shape the scenario fixture reads, plus the tid detector's own control, because an
absence detector that cannot report a difference proves nothing: it is shown counting two on a two-distinct
sample and collapsing a repeat. `heldBefore` is the same `e.observe` reader as `inFlightAfter`, read while
three items are deliberately queued and nothing is draining.

Diagnostic: `lake exe controls --runtime-http`. -/
def runtimeHttp : IO UInt32 := do
  let hooks ← Runtime.Hooks.new
  let l ← Runtime.Listener.bind (Runtime.loopback 0)
  let keep ← IO.mkRef l
  let addr ← Runtime.Listener.sockName l
  let e ← Sched.Executor.new LeanIn.Task.Item 256 1
  let srvTids ← IO.mkRef ([] : List UInt64)
  let methodRef ← IO.mkRef ""
  let uriRef ← IO.mkRef ""
  let statusRef ← IO.mkRef (0 : Nat)
  let request : ByteArray := "GET / HTTP/1.1\r\nHost: 127.0.0.1\r\nConnection: close\r\n\r\n".toUTF8
  let pinnedBody : ByteArray := "hello".toUTF8
  -- The driver's own configuration: the protocol's limits, the clock the read deadline is read from, and the
  -- deadline. The machine still sees `h1` alone, so no `Server` agent and no clock value can enter the encoder,
  -- and the response the client reads is a function of the request and the pinned head alone.
  let cfg : LeanIn.Http.Server.Config := { h1 := {}, clock := Runtime.Clock.live hooks }
  let respHead : LeanIn.Http.H1.ResponseHead :=
    { status := 200, reason := "OK", headers := #[("Content-Length", "5")] }
  statusRef.set respHead.status
  -- Our handler: it records the thread it ran on and answers with the pinned head and body. `serveConn` awaits
  -- it inline, so the thread it reads is the carrier the connection runs on.
  let handler : LeanIn.Http.Server.Handler := fun head _body => do
    let tid ← monadLift (IO.getTID : IO UInt64)
    monadLift (srvTids.modify (· ++ [tid]) : IO Unit)
    monadLift (methodRef.set (toString head.method) : IO Unit)
    monadLift (uriRef.set head.targetString : IO Unit)
    return (respHead, pinnedBody)
  -- the control: the pool holds work only until a carrier takes it, so the reader is shown a queue nothing is
  -- draining. These three no-op items are taken first when the driver starts, and they change nothing else.
  for _ in List.range 3 do e.submit (LeanIn.Task.Item.ofAction (pure ()))
  let (heldBefore, _) ← e.observe
  let serverProg : LeanIn.Task.EAsync IO.Error Unit := do
    srvTids.modify (· ++ [← monadLift (IO.getTID : IO UInt64)])
    Runtime.serveNJoin hooks l 1 (LeanIn.Http.Server.serveConn cfg · handler)
  let server ← IO.asTask (Runtime.run e serverProg) _root_.Task.Priority.dedicated
  let clientTid ← IO.getTID
  let got ← Std.Async.Async.block do
    let c ← Std.Async.TCP.Socket.Client.mk
    c.connect addr
    c.send request
    let mut acc : ByteArray := ByteArray.empty
    let mut more := true
    while more do
      match ← c.recv? 65536 with
      | none => more := false
      | some bs => acc := acc ++ bs
    c.shutdown
    return acc
  let outcome ← IO.wait server
  -- a use after the run, so the listener outlives every operation on it (the rule `--runtime-connect` found).
  let _ ← Runtime.Listener.sockName (← keep.get)
  let tids ← srvTids.get
  let distinct := distinctOf tids
  let (inFlightAfter, _) ← e.observe
  let pendingAfter ← Runtime.pending hooks
  match outcome with
  | .error err => IO.println s!"http|failed={err}"; return 1
  | .ok (.error err) => IO.println s!"http|failed={err}"; return 1
  | .ok (.ok ()) =>
    IO.println s!"http|method={← methodRef.get}|uri={← uriRef.get}|status={← statusRef.get}|got={escBytes got}|carrierThreads={distinct.length}|clientAmongServer={distinct.contains clientTid}|heldBefore={heldBefore}|inFlightAfter={inFlightAfter}|pendingHooks={pendingAfter}"
    IO.println s!"httpctl|threadsOnTwo={(distinctOf [0, 1]).length}|threadsOnRepeat={(distinctOf [7, 7]).length}"
    return 0

/-- The bytes a fresh `H1.Machine .receiving` produces for `request` and this response head and body, driven in
memory: the scenario's pinned literal comes from this same drive, and the mode reads the result's length so its
client stops at the end of a response rather than at a close. Nothing here is retyped from the fixture. -/
private def encodedResponse (request : ByteArray) (head : Std.Http.Response.Head) (body : ByteArray) :
    ByteArray :=
  Id.run do
    let mut m : Std.Http.Protocol.H1.Machine .receiving := { config := {} }
    m := m.feed request
    let mut out : ByteArray := ByteArray.empty
    let mut answered := false
    for _ in List.range 8 do
      if m.halted then break
      let (m', step) := m.step
      m := m'
      out := out ++ step.output.data.foldl (fun a x => a ++ x) ByteArray.empty
      if !answered && step.events.any (fun e => match e with
          | .endHeaders _ => true
          | _ => false) then
        answered := true
        m := m.send head |>.sendData #[Std.Http.Chunk.ofByteArray body] |>.userClosedBody
    return out

/-- The status code the client parsed out of the peer's first response line, or `0` when no status line arrived
at all. The client reads the bytes that came back over the socket rather than the head the mode handed the
handler, so `status` is the wire's own reading. -/
private def parsedStatus (bytes : ByteArray) : Nat :=
  let s := (String.fromUTF8? bytes).getD ""
  let line := (s.splitOn "\r\n").head?.getD ""
  match (line.splitOn " ").drop 1 |>.head? with
  | some code => code.toNat?.getD 0
  | none => 0

/-- **Read a clause's client socket until `want` bytes have arrived, the peer closes, or the bound fires.**

`want = some n` stops as soon as `n` bytes have accumulated, which is how clause one reads one response at a
time; `want = none` reads to end of stream, which is what clauses two and three need. The second component says
whether the bound fired. The bound is the invocation's own live-time bound — an invocation bound, never a
relation: it exists so a clause whose peer never answers cannot hang, and what it produced is recorded so a
bound-caused reading cannot pass as a peer-caused one. The same helper reads clause one's two responses and
clause three's silence, so clause three's empty reading is an absence read by the path that reported two
nonempty responses in the same run. -/
private def clientRead (c : Std.Async.TCP.Socket.Client) (want : Option Nat)
    (bound : Std.Time.Millisecond.Offset) : Std.Async.Async (ByteArray × Bool) := do
  let readLoop : Std.Async.Async (ByteArray × Bool) := do
    let mut acc : ByteArray := ByteArray.empty
    let mut more := true
    while more do
      match ← c.recv? 65536 with
      | none => more := false
      | some bs =>
        acc := acc ++ bs
        match want with
        | some n => if acc.size ≥ n then more := false
        | none => pure ()
    return (acc, false)
  Std.Async.Async.race readLoop (do Std.Async.sleep bound; return (ByteArray.empty, true))

/-- **W9's second milestone: the driver as a service — keep-alive, an answered failure, and a bounded peer.**

Three clauses, each with a listener bound by this invocation and a run of its own, in one invocation: one client
socket carries two request/response exchanges; a handler that suspends and only then returns `error` — the
raise arriving from a resumed continuation — puts a failure response on the wire; and a peer that never sends a
byte ends the connection at the mode's stated instant, read from the harness
clock. The client is deliberately `Std.Async`'s, driven by `Async.block` on this thread — a client that is not
ours is what makes the thread identities mean anything — and the server side is `LeanIn.Http.Server.serveConn` under
`Runtime.serveNJoin`, the accept loop of ours.

Records: `ka|` (clause one), `fa|` (clause two), `idle|` (clause three), plus the tid detector's own control in
`connctl|`. Each clause reports the bytes its client actually read, escaped so the field stays one token
(`\`→`\\`, CR→`\r`, LF→`\n`), the thread the server-side work ran on, and the executor's holdings before and
after — `heldBefore` being the same `e.observe` reader as `inFlightAfter`, read while three items are
deliberately queued.

The client's reads are bounded in **live time**. That bound is an invocation bound so that no clause can hang,
and it is never the relation a clause asserts: clause three asserts the harness clock's own stated instant
(`stall`), which is why it alone records `bounded=`. When the bound fires, the client closes its write side —
which is what ends the peer's read — and this mode then drives its loop in bounded rounds until the peer's run
returns, so the clause reports the peer's behaviour rather than a hang.

The drive path is ours: `Runtime.serveNJoin` is the accept loop and `LeanIn.Http.Server.serveConn` the per-connection
body, driving a `LeanIn.Http.H1` machine built from its `Limits` alone. The records the mode prints are the ones the frozen
fixture reads, so a red here is about the connection's behaviour rather than about a missing binding.

Beside the drive path, and the mode's own rather than the driver's, clause three drives its executor once past
its run: it waits for the one step the race's losing read arm leaves queued there and fires it, so the holding it records is
taken after that step rather than with it still in the queue.

Diagnostic: `lake exe controls --runtime-http-service`. -/
def runtimeHttpService : IO UInt32 := do
  let request : ByteArray := "GET / HTTP/1.1\r\nHost: 127.0.0.1\r\n\r\n".toUTF8
  let pinnedBody : ByteArray := "hello".toUTF8
  let wireHead : Std.Http.Response.Head :=
    { status := .ok, version := .v11,
      headers := Std.Http.Headers.empty.insert Std.Http.Header.Name.contentLength
        (Std.Http.Header.Value.ofString! "5") }
  let respHead : LeanIn.Http.H1.ResponseHead :=
    { status := 200, reason := "OK", headers := #[("Content-Length", "5")] }
  let expected := encodedResponse request wireHead pinnedBody
  let clientBound : Std.Time.Millisecond.Offset := 5000
  let clientTid ← IO.getTID

  -- ================= clause one: keep-alive — one connection, two exchanges =================
  let kaStart ← IO.monoNanosNow
  let hooks1 ← Runtime.Hooks.new
  let l1 ← Runtime.Listener.bind (Runtime.loopback 0)
  let keep1 ← IO.mkRef l1
  let addr1 ← Runtime.Listener.sockName l1
  let e1 ← Sched.Executor.new LeanIn.Task.Item 256 1
  let srvTids1 ← IO.mkRef ([] : List UInt64)
  let handled1 ← IO.mkRef (0 : Nat)
  let handler1 : LeanIn.Http.Server.Handler := fun _ _body => do
    let tid ← monadLift (IO.getTID : IO UInt64)
    monadLift (srvTids1.modify (· ++ [tid]) : IO Unit)
    monadLift (handled1.modify (· + 1) : IO Unit)
    return (respHead, pinnedBody)
  for _ in List.range 3 do e1.submit (LeanIn.Task.Item.ofAction (pure ()))
  let (heldBefore1, _) ← e1.observe
  let cfg1 : LeanIn.Http.Server.Config := { h1 := {}, clock := Runtime.Clock.live hooks1 }
  let server1 : LeanIn.Task.EAsync IO.Error Unit := do
    srvTids1.modify (· ++ [← monadLift (IO.getTID : IO UInt64)])
    Runtime.serveNJoin hooks1 l1 1 (LeanIn.Http.Server.serveConn cfg1 · handler1)
  let server1T ← IO.asTask (Runtime.run e1 server1) _root_.Task.Priority.dedicated
  -- The client: two exchanges on one socket. The second send is guarded because a peer that has already closed
  -- is an ordinary case for this clause, and what the clause records is the bytes, which the guard cannot change.
  let kaClient ←
    try
      Except.ok <$> Std.Async.Async.block (do
        let c ← Std.Async.TCP.Socket.Client.mk
        c.connect addr1
        c.send request
        let (first, _) ← clientRead c (some expected.size) clientBound
        let _ ← try c.send request catch _ => pure ()
        let (second, _) ← clientRead c (some expected.size) clientBound
        c.shutdown
        return (first, second))
    catch e => pure (Except.error e)
  let (first, second) := match kaClient with
    | .ok fs => fs
    | .error _ => (ByteArray.empty, ByteArray.empty)
  let kaOutcome ← IO.wait server1T
  let _ ← Runtime.Listener.sockName (← keep1.get)
  let kaUs := ((← IO.monoNanosNow) - kaStart) / 1000
  let tids1 ← srvTids1.get
  let distinct1 := distinctOf tids1
  let (inFlightAfter1, _) ← e1.observe
  let pendingAfter1 ← Runtime.pending hooks1
  match kaOutcome with
  | .error err => IO.println s!"ka|failed={err}"; return 1
  | .ok (.error err) => IO.println s!"ka|failed={err}"; return 1
  | .ok (.ok ()) =>
    IO.println s!"ka|handled={← handled1.get}|first={escBytes first}|second={escBytes second}|carrierThreads={distinct1.length}|clientAmongServer={distinct1.contains clientTid}|heldBefore={heldBefore1}|inFlightAfter={inFlightAfter1}|pendingHooks={pendingAfter1}|runUs={kaUs}"

  -- ================= clause two: a failing handler — the failure is answered on the wire =================
  let faStart ← IO.monoNanosNow
  let hooks2 ← Runtime.Hooks.new
  let l2 ← Runtime.Listener.bind (Runtime.loopback 0)
  let keep2 ← IO.mkRef l2
  let addr2 ← Runtime.Listener.sockName l2
  let e2 ← Sched.Executor.new LeanIn.Task.Item 256 1
  let srvTids2 ← IO.mkRef ([] : List UInt64)
  let cfg2 : LeanIn.Http.Server.Config := { h1 := {}, clock := Runtime.Clock.live hooks2 }
  let handler2 : LeanIn.Http.Server.Handler := fun _ _body => do
    let tid ← monadLift (IO.getTID : IO UInt64)
    monadLift (srvTids2.modify (· ++ [tid]) : IO Unit)
    -- The suspension is the point: the raise reaches the driver from a *resumed* continuation, not from the
    -- extent the handler was first called in, which is the path `VM.attempt` exists to cover.
    Runtime.VM.sleep cfg2.clock 1
    throw (IO.userError "sc20 clause two: this handler answers every request with a failure")
  for _ in List.range 3 do e2.submit (LeanIn.Task.Item.ofAction (pure ()))
  let (heldBefore2, _) ← e2.observe
  let server2 : LeanIn.Task.EAsync IO.Error Unit := do
    srvTids2.modify (· ++ [← monadLift (IO.getTID : IO UInt64)])
    Runtime.serveNJoin hooks2 l2 1 (LeanIn.Http.Server.serveConn cfg2 · handler2)
  let server2T ← IO.asTask (Runtime.run e2 server2) _root_.Task.Priority.dedicated
  let faClient ←
    try
      Except.ok <$> Std.Async.Async.block (do
        let c ← Std.Async.TCP.Socket.Client.mk
        c.connect addr2
        c.send request
        let (got, _) ← clientRead c none clientBound
        let _ ← try c.shutdown catch _ => pure ()
        return got)
    catch e => pure (Except.error e)
  let got := match faClient with
    | .ok bs => bs
    | .error _ => ByteArray.empty
  let faOutcome ← IO.wait server2T
  let _ ← Runtime.Listener.sockName (← keep2.get)
  let faUs := ((← IO.monoNanosNow) - faStart) / 1000
  let tids2 ← srvTids2.get
  let distinct2 := distinctOf tids2
  let (inFlightAfter2, _) ← e2.observe
  let pendingAfter2 ← Runtime.pending hooks2
  -- Whatever the server side did — answered, ended on an error, or died with one — the clause reports what
  -- the client observed, so the fixture's assertion reads a record rather than the invocation dying without
  -- one. `parsedStatus` reads 0 on no status line. A server-side failure that costs the client its answer
  -- fails the clause, loudly, instead of being classified away from the assertion.
  IO.println s!"fa|status={parsedStatus got}|got={escBytes got}|carrierThreads={distinct2.length}|heldBefore={heldBefore2}|inFlightAfter={inFlightAfter2}|pendingHooks={pendingAfter2}|runUs={faUs}"

  -- ================= clause three: a stalled peer — bounded at the mode's stated instant =================
  let stall : Std.Time.Millisecond.Offset := 30
  let stallMs : Nat := stall.val.toNat
  let idleStart ← IO.monoNanosNow
  let hooks3 ← Runtime.Hooks.new
  let l3 ← Runtime.Listener.bind (Runtime.loopback 0)
  let keep3 ← IO.mkRef l3
  let addr3 ← Runtime.Listener.sockName l3
  let e3 ← Sched.Executor.new LeanIn.Task.Item 256 1
  let srvTids3 ← IO.mkRef ([] : List UInt64)
  let handler3 : LeanIn.Http.Server.Handler := fun _ _body => return (respHead, pinnedBody)
  for _ in List.range 3 do e3.submit (LeanIn.Task.Item.ofAction (pure ()))
  let (heldBefore3, _) ← e3.observe
  let hc ← Runtime.HarnessClock.new
  let cfg3 : LeanIn.Http.Server.Config :=
    { h1 := {}, clock := Runtime.HarnessClock.clock hc, stallTimeout := stall }
  let server3 : LeanIn.Task.EAsync IO.Error Unit := do
    srvTids3.modify (· ++ [← monadLift (IO.getTID : IO UInt64)])
    Runtime.serveNJoin hooks3 l3 1 (LeanIn.Http.Server.serveConn cfg3 · handler3)
  let server3T ← IO.asTask (Runtime.runVirtual hc e3 server3) _root_.Task.Priority.dedicated
  -- The client connects and sends nothing, which is what leaves the driver's read to the deadline. If the
  -- invocation's bound fires first, the client closes its write side, which is what ends the peer's read.
  let idleClient ←
    try
      Except.ok <$> Std.Async.Async.block (do
        let c ← Std.Async.TCP.Socket.Client.mk
        c.connect addr3
        let (bytes, bounded) ← clientRead c none clientBound
        if bounded then
          let _ ← try c.shutdown catch _ => pure ()
        return (bytes, bounded))
    catch e => pure (Except.error e)
  let (clientGot, bounded) := match idleClient with
    | .ok rb => rb
    | .error _ => (ByteArray.empty, false)
  -- The bound fired, so the peer's run is still parked on a read that only the socket's own completions can
  -- resume: drive this loop in bounded rounds until that run returns, so the clause records the peer's behaviour
  -- rather than hanging. A round bound, not a clock read, and it changes nothing on the path where the peer's own
  -- deadline ended the connection.
  if bounded then
    let mut rounds := 0
    while (← IO.getTaskState server3T) != .finished && rounds < 500 do
      let _ ← Std.Async.Async.block (Std.Async.sleep 20)
      rounds := rounds + 1
  let idleOutcome ← IO.wait server3T
  let _ ← Runtime.Listener.sockName (← keep3.get)
  let atMs ← Runtime.HarnessClock.now hc
  let pendingAfter3 ← Runtime.HarnessClock.pending hc
  let tids3 ← srvTids3.get
  let distinct3 := distinctOf tids3
  -- **Drive once more, then read.** A deadline that wins sets the `Task.Async` computation token, so the
  -- loser's later steps are skipped; an already-submitted raw peer read is not withdrawn, though, and can
  -- still complete after the peer's run, enqueueing the stamped continuation here as an item nothing else
  -- takes. Wait for that one item (a bounded live-time wait, because the socket's completion lands after the
  -- run returns rather than during it) and fire it, so what this clause reads below is the queue *after* the
  -- leftover has been taken. `Item.fire` sees the cancelled token and skips its action, so no residual
  -- executor work remains: not a claim that the raw I/O registration or operation is cancelled, nor that
  -- another item's behaviour changes. A dropped step that was *not* this loser would still be held
  -- afterwards, and a step that resumed the connection loop would write to the wire and queue again.
  let driveStart ← IO.monoNanosNow
  let mut leftover? ← e3.takeFor 0
  while leftover?.isNone && (← IO.monoNanosNow) - driveStart < 200000000 do
    IO.sleep 1
    leftover? ← e3.takeFor 0
  if let some leftover := leftover? then leftover.fire
  let (inFlightAfter3, _) ← e3.observe
  let pendingHooks3 ← Runtime.pending hooks3
  let idleUs := ((← IO.monoNanosNow) - idleStart) / 1000
  match idleOutcome with
  | .error err => IO.println s!"idle|failed={err}"; return 1
  | .ok (.error err) => IO.println s!"idle|failed={err}"; return 1
  | .ok (.ok ()) =>
    IO.println s!"idle|stall={stallMs}|at={atMs}|pendingAfter={pendingAfter3}|clientGot={escBytes clientGot}|bounded={if bounded then "yes" else "no"}|carrierThreads={distinct3.length}|clientAmongServer={distinct3.contains clientTid}|heldBefore={heldBefore3}|inFlightAfter={inFlightAfter3}|pendingHooks={pendingHooks3}|runUs={idleUs}"

  IO.println s!"connctl|threadsOnTwo={(distinctOf [0, 1]).length}|threadsOnRepeat={(distinctOf [7, 7]).length}"
  return 0



/-- **M3's evidence: time as an effect in a compiled machine, at the harness clock's stated instants.**

Two clauses in one invocation, each with its own listener, executor and `HarnessClock`, and each served by a
compiled machine whose close submission the run awaits through a `Join` cell (so the run holds until the
machine's terminal step, not its first suspension; the client's read to EOF observes the socket's closure). Clause one is `amDelayed` — read a request, `sleepRaw` `d` on the harness
clock, answer, close: the client must see nothing until the clock reaches `d`, and then the echo, so its
readings are the affirmative control for clause two's empty one. Clause two is `amStall` — a `recvTimeoutRaw`
race against the same stated instant: the client never sends, so the deadline wins, the connection ends with
nothing written, and `at` is the harness clock's own reading when the run has returned, exactly SC20-O3's
relation. The client is deliberately `Std.Async`'s, driven by `Async.block` on this thread.

Records: `dl|` and `st|`, each with the stated instant, `at`, the bytes its client read (escaped as
`escBytes` does), `pendingAfter` (the harness clock's own outstanding-timer count), the server-side threads,
and the executor's holdings (`heldBefore` read while three items are deliberately queued).

Diagnostic: `lake exe controls --runtime-machine-time`. -/
def runtimeMachineTime : IO UInt32 := do
  let request : ByteArray := "tick tock".toUTF8
  let d : Std.Time.Millisecond.Offset := 30
  let dMs : Nat := d.val.toNat
  let clientBound : Std.Time.Millisecond.Offset := 5000

  -- ================= clause one: a delayed answer (`dl|`) — sleepRaw on the harness clock =================
  let dlStart ← IO.monoNanosNow
  let hooks1 ← Runtime.Hooks.new
  let l1 ← Runtime.Listener.bind (Runtime.loopback 0)
  let keep1 ← IO.mkRef l1
  let addr1 ← Runtime.Listener.sockName l1
  let e1 ← Sched.Executor.new LeanIn.Task.Item 256 1
  let srvTids1 ← IO.mkRef ([] : List UInt64)
  for _ in List.range 3 do e1.submit (LeanIn.Task.Item.ofAction (pure ()))
  let (heldBefore1, _) ← e1.observe
  let hc1 ← Runtime.HarnessClock.new
  let push1 := Runtime.sharedPush e1
  -- The reusable wake composition: arming from the loop's thread also nudges the parked driver through the
  -- inject (see `HarnessClock.clockWithWake`'s own note).
  let clock1 := Runtime.HarnessClock.clockWithWake hc1 push1
  let server1 : LeanIn.Task.EAsync IO.Error Unit := do
    srvTids1.modify (· ++ [← monadLift (IO.getTID : IO UInt64)])
    let c ← Runtime.Listener.accept l1 hooks1
    amDelayed c clock1 d
  let server1T ← IO.asTask (Runtime.runVirtual hc1 e1 server1) _root_.Task.Priority.dedicated
  let dlClient ←
    try
      Except.ok <$> Std.Async.Async.block (do
        let c ← Std.Async.TCP.Socket.Client.mk
        c.connect addr1
        c.send request
        let (bytes, bounded) ← clientRead c none clientBound
        if bounded then
          let _ ← try c.shutdown catch _ => pure ()
        return (bytes, bounded))
    catch e => pure (Except.error e)
  let (got1, bounded1) := match dlClient with
    | .ok rb => rb
    | .error _ => (ByteArray.empty, true)
  -- Grace rounds on **both** paths: on the normal one the run has already completed (the machine's terminal
  -- step resolved the cell the run awaits), so these rounds cost nothing; on a bounded read they give the
  -- stalled run a bounded chance to finish. Expiry is loud rather than an unbounded wait.
  let mut rounds1 := 0
  while (← IO.getTaskState server1T) != .finished && rounds1 < 500 do
    let _ ← Std.Async.Async.block (Std.Async.sleep 20)
    rounds1 := rounds1 + 1
  if (← IO.getTaskState server1T) != .finished then
    IO.eprintln "runtime-machine-time: the delayed-answer server is still running after the grace rounds"
    return 1
  let dlOutcome ← IO.wait server1T
  let _ ← Runtime.Listener.sockName (← keep1.get)
  let at1Ms ← Runtime.HarnessClock.now hc1
  let pendingAfter1 ← Runtime.HarnessClock.pending hc1
  let tids1 ← srvTids1.get
  let distinct1 := distinctOf tids1
  let (inFlightAfter1, _) ← e1.observe
  let dlUs := ((← IO.monoNanosNow) - dlStart) / 1000
  match dlOutcome with
  | .error err => IO.println s!"dl|failed={err}"; return 1
  | .ok (.error err) => IO.println s!"dl|failed={err}"; return 1
  | .ok (.ok ()) =>
    IO.println s!"dl|delay={dMs}|at={at1Ms}|got={escBytes got1}|bounded={if bounded1 then "yes" else "no"}|pendingAfter={pendingAfter1}|carrierThreads={distinct1.length}|heldBefore={heldBefore1}|inFlightAfter={inFlightAfter1}|runUs={dlUs}"

  -- ================= clause two: a stalled peer (`st|`) — the recvTimeout race on the harness clock ==========
  let stStart ← IO.monoNanosNow
  let hooks2 ← Runtime.Hooks.new
  let l2 ← Runtime.Listener.bind (Runtime.loopback 0)
  let keep2 ← IO.mkRef l2
  let addr2 ← Runtime.Listener.sockName l2
  let e2 ← Sched.Executor.new LeanIn.Task.Item 256 1
  let srvTids2 ← IO.mkRef ([] : List UInt64)
  for _ in List.range 3 do e2.submit (LeanIn.Task.Item.ofAction (pure ()))
  let (heldBefore2, _) ← e2.observe
  let hc2 ← Runtime.HarnessClock.new
  let push2 := Runtime.sharedPush e2
  let server2 : LeanIn.Task.EAsync IO.Error Unit := do
    srvTids2.modify (· ++ [← monadLift (IO.getTID : IO UInt64)])
    let c ← Runtime.Listener.accept l2 hooks2
    amStall c (Runtime.HarnessClock.clockWithWake hc2 push2) d
  let server2T ← IO.asTask (Runtime.runVirtual hc2 e2 server2) _root_.Task.Priority.dedicated
  let stClient ←
    try
      Except.ok <$> Std.Async.Async.block (do
        let c ← Std.Async.TCP.Socket.Client.mk
        c.connect addr2
        let (bytes, bounded) ← clientRead c none clientBound
        if bounded then
          let _ ← try c.shutdown catch _ => pure ()
        return (bytes, bounded))
    catch e => pure (Except.error e)
  let (got2, bounded2) := match stClient with
    | .ok rb => rb
    | .error _ => (ByteArray.empty, true)
  -- Grace rounds on **both** paths: on the normal one the run has already completed (the machine's terminal
  -- step resolved the cell the run awaits), so these rounds cost nothing; on a bounded read they give the
  -- stalled run a bounded chance to finish. Expiry is loud rather than an unbounded wait.
  let mut rounds2 := 0
  while (← IO.getTaskState server2T) != .finished && rounds2 < 500 do
    let _ ← Std.Async.Async.block (Std.Async.sleep 20)
    rounds2 := rounds2 + 1
  if (← IO.getTaskState server2T) != .finished then
    IO.eprintln "runtime-machine-time: the stalled-peer server is still running after the grace rounds"
    return 1
  let stOutcome ← IO.wait server2T
  let _ ← Runtime.Listener.sockName (← keep2.get)
  let at2Ms ← Runtime.HarnessClock.now hc2
  let pendingAfter2 ← Runtime.HarnessClock.pending hc2
  let tids2 ← srvTids2.get
  let distinct2 := distinctOf tids2
  let (inFlightAfter2, _) ← e2.observe
  let stUs := ((← IO.monoNanosNow) - stStart) / 1000
  match stOutcome with
  | .error err => IO.println s!"st|failed={err}"; return 1
  | .ok (.error err) => IO.println s!"st|failed={err}"; return 1
  | .ok (.ok ()) =>
    IO.println s!"st|stall={dMs}|at={at2Ms}|clientGot={escBytes got2}|bounded={if bounded2 then "yes" else "no"}|pendingAfter={pendingAfter2}|carrierThreads={distinct2.length}|heldBefore={heldBefore2}|inFlightAfter={inFlightAfter2}|runUs={stUs}"
  return 0

/-- Throwaway, for W1's outbound direction and W3's acceptance: do `Std.Async`'s leaves work through the seam,
and do timers overlap on one carrier? Four tasks each awaiting a 50ms `Std.Async.sleep` should take about 50ms,
not 200 — which is what distinguishes a timer from `IO.sleep` (which blocks the thread). -/
def runtimeSleep : IO UInt32 := do
  let e ← Sched.Executor.new LeanIn.Task.Item 256 1
  let hooks ← Runtime.Hooks.new
  let carrier ← IO.getTID
  let t0 ← IO.monoNanosNow
  let _ ← Runtime.run e (do
    let hs ← (List.range 4).mapM (fun _ =>
      LeanIn.Task.Async.spawn (Runtime.awaitAsync hooks (Std.Async.sleep 50)))
    for h in hs do let _ ← LeanIn.Task.Async.await h
    pure ())
  let t1 ← IO.monoNanosNow
  IO.println s!"sleep   : 4 x 50ms via Std.Async on carrier {carrier}: {(t1 - t0) / 1000000}ms (serial would be 200ms)"
  return 0

/-- **SC6 — real work on the runtime, and the thread identities it ran on.**

One carrier: the driver, the spawned child's body, and the continuation that resumed after the external
completion are the *same* thread, and the client starts no thread of its own. The external completion is the
affirmative control that makes that measurement mean something: it finishes on a pool worker, its thread is
recorded, and all that thread does is enqueue — so the record can tell "one carrier" from "one thread because
nothing else was in the picture".

Every identity is read where it happens: inside the step that ran, and inside the completion that fired. -/
def runtimeThreads : IO UInt32 := do
  let e ← Sched.Executor.new LeanIn.Task.Item 256 1
  let caller ← IO.getTID
  let steps ← IO.mkRef ([] : List UInt64)
  let external ← IO.mkRef (0 : UInt64)
  let hooks ← Runtime.Hooks.new
  let step : LeanIn.Task.Async Unit := LeanIn.Task.Async.ofIO do
    steps.modify (· ++ [← IO.getTID])
  -- A child spawned from inside the body and awaited, and an external completion from the pool.
  let child : LeanIn.Task.Async Nat := do
    let _ ← step
    return 11
  -- The completion is observed where it happens: in the task's own body, on the pool worker running it, so
  -- the conversion in `LeanIn.Runtime.Leaf` can be used unmodified.
  let ext ← IO.asTask (do external.set (← IO.getTID); IO.sleep 20; return (5 : Nat)) _root_.Task.Priority.dedicated
  let prog : LeanIn.Task.Async Nat := do
    let h ← LeanIn.Task.Async.spawn child
    let a ← LeanIn.Task.Async.await h
    let b ← Runtime.awaitTask hooks ext
    let _ ← step
    return (a + b)
  let v ← Runtime.run e prog
  let st ← e.snapshot
  let ids := (← steps.get).map toString
  IO.println s!"exec|runtime|caller={caller}|steps=[{String.intercalate "," ids}]|external={← external.get}|value={v}|remaining={st.held}"
  return 0

/-- **SC4's scripted input.** The identity each position delivers, decided by the seed and the script name —
so the same inputs are reproducible from the seed, and the alternate script is a different *input* rather
than a different answer.

Position `3` is where the main script's failing task sits: it delivers identity `1`, and that is the one that
fails. The alternate delivers `2` there and is otherwise the same script, so the two traces differ by
construction rather than by chance. -/
def replayIdentity (seed : Nat) (script : String) (p : Nat) : Nat :=
  if p = 3 then (if script = "alternate" then 2 else 1)
  else (seed * 31 + p * 7) % 4 + 10

/-- **SC4 — replay a scripted run and record the canonical trace it produced.**

Every value is driven through the executor and read back out of it, and nothing here reads a clock or starts
a thread, so two runs of the same seed and script produce the same bytes. That identity is the whole claim,
and binding the failure to its own position and identity is what makes it a debugging contract rather than a
comparison of two similar strings. -/
def executorReplay (seed : Nat) (script : String) : IO UInt32 := do
  let e ← Sched.Executor.new Nat 256 1
  let mut trace : List String := []
  for p in List.range 5 do
    let id := replayIdentity seed script p
    e.submit id
    let got ← e.take
    let st ← e.snapshot
    match got with
    | some x =>
      if p = 3 then
        -- The staged failing body: the identity this position delivers is the one that fails, so the record
        -- carries the failure at its own position and identity rather than somewhere in the trace.
        trace := trace ++ [s!"op=fail|pos={p}|task={x}|out=error:seeded-failure"]
      else
        trace := trace ++ [s!"op=take|pos={p}|task={x}|out=taken{st.taken}"]
    | none =>
      trace := trace ++ [s!"op=take|pos={p}|task=-|out=none"]
  IO.println s!"exec|replay|seed={seed}|{String.intercalate ";" trace}"
  return 0

/-- **SC5 — the bounded ring, the LIFO allowance and the overflow, in two phases.**

Phase one submits `0..256` before taking any, so the 257th submission crosses the ring's capacity, and then
drains that whole batch. Phase two is a fresh tick — the allowance's clock — where two identities are staged
as FIFO work and a root local `spawn` puts `400` in the slot; each body then locally spawns the next, so the
three polls and the flush that follows them happen in one tick.

Nothing here writes a ring, slot or counter. Every value is read out of a public operation, and each slot
observation is the one the take reported at its own decision — which is what an allowance test that never
populated the slot cannot produce. -/
def executorQueue : IO UInt32 := do
  let e ← Sched.Executor.new Nat 256 1
  let staged ← IO.mkRef ([] : List Nat)
  let delivered ← IO.mkRef ([] : List Nat)
  let phase ← IO.mkRef ([] : List String)
  let fifo ← IO.mkRef ([] : List Nat)

  -- Phase one: stage the whole batch, then drain it.
  let batch : List Nat := List.range 257
  for x in batch do
    e.submit x
    staged.modify (· ++ [x])
  for _ in batch do
    match ← e.take with
    | some x => fifo.modify (· ++ [x]); delivered.modify (· ++ [x])
    | none   => pure ()
  phase.modify (· ++ ["batch-drained"])

  -- Phase two: a fresh tick, then two FIFO stagings and the root local spawn.
  e.tick
  phase.modify (· ++ ["tick-start"])
  e.submit 300
  staged.modify (· ++ [300])
  phase.modify (· ++ ["stage:300"])
  e.submit 301
  staged.modify (· ++ [301])
  phase.modify (· ++ ["stage:301"])
  e.spawn 400
  staged.modify (· ++ [400])
  phase.modify (· ++ ["spawn:400"])

  let lifo ← IO.mkRef ([] : List Nat)
  let flush ← IO.mkRef ([] : List Nat)
  let slotBefore ← IO.mkRef ([] : List String)
  let mut polls : Nat := 0
  let mut flushed : Bool := false
  let mut go := true
  while go do
    let r ← e.takeReport
    match r.item with
    | none => go := false
    | some x =>
      -- The scheduler's own observation at this decision, keyed by the poll count: a poll advances it, and
      -- the flush does not, because flushing the slot is not serving from it.
      match r.observed with
      | some o => slotBefore.modify (· ++ [s!"{polls}:{o}"])
      | none   => pure ()
      match r.served with
      | Sched.Served.slot    => lifo.modify (· ++ [x]); polls := polls + 1
      | Sched.Served.flushed => flushed := true; flush.modify (· ++ [x])
      | Sched.Served.queue   => if flushed then flush.modify (· ++ [x]) else pure ()
      delivered.modify (· ++ [x])
      -- The body that just ran: the chained continuations locally spawn the next of 401..403.
      if 400 ≤ x && x < 403 then
        e.spawn (x + 1)
        staged.modify (· ++ [x + 1])

  let st ← e.snapshot
  IO.println (s!"exec|queue|staged=[{String.intercalate "," ((← staged.get).map toString)}]"
    ++ s!"|phase={String.intercalate "," (← phase.get)}"
    ++ s!"|fifo=[{String.intercalate "," ((← fifo.get).map toString)}]"
    ++ s!"|lifo=[{String.intercalate "," ((← lifo.get).map toString)}]"
    ++ s!"|flush=[{String.intercalate "," ((← flush.get).map toString)}]"
    ++ s!"|slotBefore=[{String.intercalate "," (← slotBefore.get)}]"
    ++ s!"|delivered=[{String.intercalate "," ((← delivered.get).map toString)}]"
    ++ s!"|remaining={st.held}")
  return 0

/-- The decision kind's own name in SC21's record: the LIFO slot served it, the spent slot was cleared for the
shared list, or neither — the ring. -/
private def servedName : Sched.Served → String
  | Sched.Served.slot    => "slot"
  | Sched.Served.flushed => "flushed"
  | Sched.Served.queue   => "queue"

/-- **SC21 — a chain that keeps the LIFO slot occupied is interrupted at the allowance.**

The take's decision refreshes the allowance when it was not a slot serve, so `lifoPolls` counts *consecutive*
slot polls: a chain that keeps the slot filled is interrupted at the cap, while a chain that yields is not
demoted. This mode reads that schedule off one chain that never yields. The root is locally `spawn`ed, so it
takes the slot, and every link a take delivers is continued by locally `spawn`ing its successor, so the slot is
re-filled before the next decision; one marker is submitted to the ring before the chain starts, because a
flush has to have something of the ring's to serve.

Every value is read out of the executor's own take at its own decision: `served` is which way each decision
went, `observed` is the slot's occupant as that decision read it (`-` when it found the slot empty),
`delivered` is the item each take returned, in order, and `flushes` counts the decisions that cleared a spent
slot. `links` is this mode's chain length; `cap` is read from the pool's own allowance rather than stated here,
and `held`, `taken` and `pendingAfter` are the composition's accounting — work still held, work taken, and the
shared list's own length — so a flush that lost its item would show up in them. This mode writes no ring, slot
or counter, and reads no clock towards any relation: `runUs` is printed and never asserted.

Diagnostic: `lake exe controls --executor-lifo-turns`. -/
def executorLifoTurns : IO UInt32 := do
  -- The drive path's three identities: the chain is `first .. first + links - 1`, and the ring marker is
  -- submitted before the chain starts.
  let links : Nat := 12
  let first : Nat := 400
  let marker : Nat := 300
  let e ← Sched.Executor.new Nat 256 1
  let served ← IO.mkRef ([] : List String)
  let observed ← IO.mkRef ([] : List String)
  let delivered ← IO.mkRef ([] : List Nat)
  let mut flushes : Nat := 0
  let t0 ← IO.monoNanosNow
  e.submit marker
  e.spawn first
  let mut go := true
  while go do
    let r ← e.takeReport
    match r.item with
    | none => go := false
    | some x =>
      served.modify (· ++ [servedName r.served])
      observed.modify (· ++ [match r.observed with
        | some o => toString o
        | none   => "-"])
      delivered.modify (· ++ [x])
      if r.served == Sched.Served.flushed then flushes := flushes + 1
      -- The chain's step: the link this take delivered is continued by locally spawning its successor, which
      -- takes the slot again before the next decision. The last link and the ring marker have no successor.
      if first ≤ x && x < first + links - 1 then e.spawn (x + 1)
  let t1 ← IO.monoNanosNow
  let st ← e.snapshot
  let allowance := (st.workers[0]?.map (·.lifoCap)).getD 0
  IO.println (s!"lifoturn|cap={allowance}|links={links}"
    ++ s!"|served=[{String.intercalate "," (← served.get)}]"
    ++ s!"|observed=[{String.intercalate "," (← observed.get)}]"
    ++ s!"|delivered=[{String.intercalate "," ((← delivered.get).map toString)}]"
    ++ s!"|flushes={flushes}|held={st.held}|taken={st.taken}|pendingAfter={st.inject.length}"
    ++ s!"|runUs={(t1 - t0) / 1000}")
  return 0

/-- **SC22, the route clause's arm — where a step's deferred enqueue lands.**

One executor with two workers, and the two roles kept apart so that the arrival is a reading rather than a
race. Worker `1` is a genuinely started carrier — a dedicated thread of its own running
`Executor.workerLoop`, its tid recorded in the carrier counters as it entered the loop — and worker `0` has
**no** loop of its own: the invocation's thread stands in for it, placing the creator's step on worker `0`'s
queue and firing it with index `0`, which is the driver's own convention (`Runtime.blockOn` drives worker `0`
on the calling thread).

The creator's step is the task layer's own deferred registration: `Async.await` on a cell with no value yet,
run with worker `0`'s routes. It registers a continuation and returns, and what the registration holds is the
*waiter's* context — its token, its ambient context, and the runtime's route **table** — not a resolved route:
the route it will re-enqueue on is read when a worker fires it. The resolving step is an item on worker `1`'s
queue, delivered through the shared route and fired by worker `1`'s carrier — a peer thread relative to the
creator — which resolves that cell with **its own** route, so the deferred continuation is delivered as an item
on worker `1`'s own queue, and then reads the composition's own pools. Reading them inside the resolving step,
before that step returns, is what makes the pool a reading of an enqueue rather than of a race: worker `1`
cannot take from its own queue while it is inside the step, and worker `0` has no loop to take with.

**The completion clause's arm — a chain across carriers that must complete.** One executor with two started
carriers. The creator's root is delivered through the shared route, and it delivers its link the same way, so a
peer carrier runs the link rather than the creator. The creator holds inside its own step until that link has
started, which is what keeps the link out of the creator's own reach — a carrier inside a step cannot take from
the shared list — and the link holds until the creator's carrier is **parked**, read from the composition's own
`parked` count, so the completion arrives at a wait that the wake has to reach. The link's completion resolves
the creator's cell, and the creator's continuation runs wherever that resolution's route sends it.

Both arms' waits are **round counts**, never clocks: a round is a locked read of a cell the composition owns
(`Join.value?`, `Executor.observe`), so an expiry is a reading — `resolverRounds` and `completionRounds` at the
bound — and not a hang, and the shell's watchdog stays only a hang bound. The bound is larger than the
dispatch-only modes' 20000 because these arms wait for a dedicated thread's *first shift* and for an item to be
taken and run on it: thousands of lock acquisitions' worth of work rather than one wake, which is what the
record's round fields let a reader see.

Diagnostic: `lake exe controls --executor-route [--bound N]`. -/
def executorRoute (bound : Nat) : IO UInt32 := do
  let runStart ← IO.monoNanosNow
  -- the two roles of the route arm, and the two workers they run on: distinct, which is the clause's premise
  let creatorIdx : Nat := 0
  let firerIdx : Nat := 1
  let er ← Sched.Executor.newMetered Task.Item 256 2
  -- worker 0's loop is this thread, playing the driver's part; worker 1 gets a thread of its own
  let creatorTid ← IO.getTID
  let peer ← IO.asTask (er.workerLoop (fun idx it => it.fireWith idx) firerIdx)
    _root_.Task.Priority.dedicated
  -- the firing worker's identity, from the carrier counters' own tid, recorded as its loop began
  let mut firerTid : UInt64 := 0
  let mut tidRounds : Nat := 0
  while firerTid == 0 && tidRounds < bound do
    let cs := (← er.metrics).getD []
    firerTid := (cs[firerIdx]?.map (·.tid)).getD 0
    tidRounds := tidRounds + 1
  let poolAt (s : Sched.Snapshot Task.Item 256) (i : Nat) : Nat :=
    (s.workers[i]?.map (·.inFlight)).getD 0
  let cell ← Task.Join.new (α := Unit)
  let tokCreator ← Task.Cancel.new
  let tokResolver ← Task.Cancel.new
  let creatorPoolAfter ← IO.mkRef (0 : Nat)
  let firerPoolAfter ← IO.mkRef (0 : Nat)
  let pendingAfter ← IO.mkRef (0 : Nat)
  let continuationTid ← IO.mkRef (0 : UInt64)
  let continuationRuns ← IO.mkRef (0 : Nat)
  -- The mode's own two gates, as cells rather than bare flags: every wait below reads them through the
  -- cell's lock, so a round is a lock acquisition — the shape `--runtime-carriers`' round counts have — and a
  -- write by the peer is visible to the reader rather than left to a spin over an unsynchronised field.
  let resolvedCell ← Task.Join.new (α := Unit)
  let continuationCell ← Task.Join.new (α := Unit)
  let before ← er.snapshot
  let creatorPoolBefore := poolAt before creatorIdx
  let firerPoolBefore := poolAt before firerIdx
  -- the creator: worker 0's own deferred registration. The continuation it leaves is delivered *as an item*
  -- by the step that resolves the cell, on that step's own route.
  let creatorProg : Task.Async Unit := Task.Async.await (⟨cell, tokCreator⟩ : Task.Task Unit)
  let creatorItem := Task.Item.ofIndexed (some tokCreator)
    (fun _ => Runtime.fired tokCreator er creatorProg (fun _ ctx' => do
      continuationTid.set (← IO.getTID)
      continuationRuns.modify (· + 1)
      Task.Join.resolve continuationCell ctx'.resume ()) creatorIdx)
  er.submitLocal creatorIdx (Task.Item.sendable creatorItem)
  match ← er.takeFor creatorIdx with
  | some it => it.fireWith creatorIdx
  | none    => pure ()
  -- the resolver: fired by the peer carrier, resolving the cell — which delivers the creator's continuation as
  -- an item on *this* worker's own route, its local pool — and then reading the pools before it returns
  let resolverProg : Task.Async Unit := ⟨fun k ctx => do
    Task.Join.resolve cell ctx.resume ()
    let s ← er.snapshot
    creatorPoolAfter.set (poolAt s creatorIdx)
    firerPoolAfter.set (poolAt s firerIdx)
    pendingAfter.set s.inject.length
    Task.Join.resolve resolvedCell ctx.resume ()
    k () ctx⟩
  let resolverItem := Task.Item.ofIndexed (some tokResolver)
    (fun i => Runtime.fired tokResolver er resolverProg (fun _ _ => pure ()) i)
  er.pushInject (Task.Item.sendable resolverItem)
  let mut resolverRounds : Nat := 0
  let mut resolvedNow := false
  while !resolvedNow && resolverRounds < bound do
    resolvedNow := (← Task.Join.value? resolvedCell).isSome
    if !resolvedNow then resolverRounds := resolverRounds + 1
  -- worker 0 has no loop: whatever landed in its own pool is taken here, by this thread, so "it landed on
  -- the creator's pool" is what the run reads rather than something inferred from where the item ran
  match ← er.takeFor creatorIdx with
  | some it => it.fireWith creatorIdx
  | none    => pure ()
  let mut contRounds : Nat := 0
  let mut contNow := false
  while !contNow && contRounds < bound do
    contNow := (← Task.Join.value? continuationCell).isSome
    if !contNow then contRounds := contRounds + 1
  let routeUs := ((← IO.monoNanosNow) - runStart) / 1000
  er.stop
  match ← IO.wait peer with
  | .ok _    => pure ()
  | .error _ => pure ()
  IO.println s!"sc22cfg|bound={bound}|p=2|creator={creatorIdx}|firer={firerIdx}"
  IO.println (s!"route|creator={creatorIdx}|firer={firerIdx}|p=2"
    ++ s!"|creatorPoolBefore={creatorPoolBefore}|creatorPoolAfter={← creatorPoolAfter.get}"
    ++ s!"|firerPoolBefore={firerPoolBefore}|firerPoolAfter={← firerPoolAfter.get}"
    ++ s!"|pendingAfter={← pendingAfter.get}|creatorTid={creatorTid}|firerTid={firerTid}"
    ++ s!"|continuationTid={← continuationTid.get}|continuationRuns={← continuationRuns.get}"
    ++ s!"|resolverRounds={resolverRounds}|bound={bound}|runUs={routeUs}")
  -- the completion arm, on its own executor so the two arms' parked counts cannot see each other
  let crossStart ← IO.monoNanosNow
  let ec ← Runtime.Executor.newMetered 256 2
  let hc := Runtime.handle ec
  let c ← Runtime.startCarriers ec 2
  let tokCross ← Task.Cancel.new
  let childStarted ← Task.Join.new (α := Unit)
  let childTid ← IO.mkRef (0 : UInt64)
  let creatorTidX ← IO.mkRef (0 : UInt64)
  let continuationTidX ← IO.mkRef (0 : UInt64)
  let creatorRuns ← IO.mkRef (0 : Nat)
  let childRuns ← IO.mkRef (0 : Nat)
  let continuationRunsX ← IO.mkRef (0 : Nat)
  let waiterParked ← IO.mkRef (0 : Nat)
  let finished ← Task.Join.new (α := Unit)
  -- the link, delivered through the shared route: it records where it ran, then holds until the creator's
  -- carrier is parked. Neither link is inside a park when the hold begins, so the first nonzero reading of
  -- the composition's own parked count is the creator's — the wait the completion has to reach.
  let childProg : Task.Async Unit := do
    let push ← Task.Async.push
    Task.Async.ofIO do
      childTid.set (← IO.getTID)
      childRuns.modify (· + 1)
      Task.Join.resolve childStarted push ()
    Task.Async.ofIO do
      let mut seen : Nat := 0
      let mut i : Nat := 0
      while seen == 0 && i < bound do
        let (_, pk) ← ec.observe
        seen := pk
        i := i + 1
      waiterParked.set seen
  let creatorProg : Task.Async Unit := do
    let h ← Runtime.Handle.spawn hc Runtime.Priority.normal childProg
    -- hold inside this step until the link has started, so the link is a peer carrier's to take
    Task.Async.ofIO do
      let mut seen := false
      let mut i : Nat := 0
      while !seen && i < bound do
        seen := (← Task.Join.value? childStarted).isSome
        if !seen then i := i + 1
    let _ ← Task.Async.await h
    pure ()
  let creatorItem := Task.Item.ofIndexed (some tokCross)
    (fun i => do
      creatorTidX.set (← IO.getTID)
      creatorRuns.modify (· + 1)
      Runtime.fired tokCross ec creatorProg (fun _ ctx' => do
        continuationTidX.set (← IO.getTID)
        continuationRunsX.modify (· + 1)
        Task.Join.resolve finished ctx'.resume ()) i)
  ec.pushInject (Task.Item.sendable creatorItem)
  let mut completionRounds : Nat := 0
  while (← Task.Join.value? finished).isNone && completionRounds < bound do
    completionRounds := completionRounds + 1
  let completed := (← Task.Join.value? finished).isSome
  let ctid ← creatorTidX.get
  let chid ← childTid.get
  let ktid ← continuationTidX.get
  let crossed := chid != 0 && ctid != 0 && chid != ctid
  let cruns ← creatorRuns.get
  let chruns ← childRuns.get
  let kruns ← continuationRunsX.get
  let wp ← waiterParked.get
  -- the readings are taken before the stop: a stop drains, and what a drain runs is not what the chain did
  c.stop
  c.join
  let (heldAfter, _) ← ec.observe
  let crossUs := ((← IO.monoNanosNow) - crossStart) / 1000
  IO.println (s!"crossing|p=2|completed={if completed then 1 else 0}"
    ++ s!"|creatorRuns={cruns}|childRuns={chruns}|continuationRuns={kruns}"
    ++ s!"|crossed={if crossed then 1 else 0}|waiterParked={wp}"
    ++ s!"|creatorTid={ctid}|childTid={chid}|continuationTid={ktid}"
    ++ s!"|completionRounds={completionRounds}|bound={bound}|heldAfterStop={heldAfter}|runUs={crossUs}")
  (← IO.getStdout).flush
  return 0

/-- **The timeout's loser, on harness clocks only.**

A computation spawned under a deadline at virtual instant 10 records that it started, sleeps to instant 30, and
would record that it resumed; the root stays live to instant 50, so the loser's own wake has the run rather than
waiting behind the root. `after=false` at instant 50 is the claim — the loser recorded nothing after its wake
because the deadline that won stopped it. `start=true` says the same recorder saw the loser begin, which is a
control for that recorder rather than for the `after` detector.

The `after` detector's affirmative control is the same action, executed for real on a separate harness clock:
`recordAfter` appends `"after"`, a virtual sleep runs it on a clean clock, and the same `List.contains` reads
that marker through the same event reference before the reference is cleared for the losing run. The two
readings differ only in whether the action ran, so an absent marker is about the loser and not about a detector
that cannot fire. Nothing here reads a live clock, sleeps for real or touches the loop.

Diagnostic: `lake exe controls --runtime-time-loser`; the same record is the last row of `--runtime-time`. -/
def timeoutLoserObservation : IO Unit := do
  let events ← IO.mkRef ([] : List String)
  let recordAfter : LeanIn.Task.Async Unit :=
    LeanIn.Task.Async.ofIO (events.modify (· ++ ["after"]) : IO Unit)
  -- The detector's affirmative control, on its own clock: the same action, the same reference, the same read.
  let hcControl ← Runtime.HarnessClock.new
  let cControl := Runtime.HarnessClock.clock hcControl
  let eControl ← Sched.Executor.new LeanIn.Task.Item 256 1
  let _ ← Runtime.runVirtual hcControl eControl (do
    Runtime.sleep cControl 5
    recordAfter)
  let afterDetectedWhenPresent := (← events.get).contains "after"
  events.set []
  -- The losing run: the deadline wins at instant 10, the loser sleeps to instant 30 and takes the same action
  -- after it, and the root stays live past the loser's wake.
  let hcLoser ← Runtime.HarnessClock.new
  let cLoser := Runtime.HarnessClock.clock hcLoser
  let eLoser ← Sched.Executor.new LeanIn.Task.Item 256 1
  let loser : LeanIn.Task.Async Unit := do
    events.modify (· ++ ["start"])
    Runtime.sleep cLoser 30
    recordAfter
  let outcome ← Runtime.runVirtual hcLoser eLoser (do
    let outcome ← Runtime.withTimeout cLoser 10 loser
    Runtime.sleep cLoser 40
    pure outcome)
  let advanced ← Runtime.HarnessClock.now hcLoser
  let recorded ← events.get
  let started := recorded.contains "start"
  let after := recorded.contains "after"
  let outcomeStr := match outcome with | none => "none" | some _ => "some"
  IO.println s!"timeoutLoser|outcome={outcomeStr}|start={started}|after={after}|advanced={advanced}|afterDetectedWhenPresent={afterDetectedWhenPresent}"

/-- **W3's evidence: timers on our carriers.**

`n` sleepers and one late spawn, with the *order* of the events doing the work a clock would otherwise be asked
to do. Every sleeper records that it started before it sleeps and that it woke afterwards, and a task spawned
while all `n` sleeps are pending records that it ran. If the sleeps occupied the carrier rather than parking on
a timer, the first sleeper's wake would land between the first two starts — so "everything before the first
wake is a start" *is* the overlap, read from the recorded order and not from elapsed time. The two timeout
outcomes are deterministic for the same reason: one inner computation never finishes and must time out, the
other finishes immediately and must not. The measured row is printed and never asserted, for the reason the
socket check gives.

The last record is the timeout's other half, read from harness clocks rather than from elapsed time:
`timeoutLoserObservation` runs the loser and its detector's affirmative control, and prints the same record the
dedicated `--runtime-time-loser` mode prints.

Diagnostic: `lake exe controls --runtime-time`. -/
def runtimeTime : IO UInt32 := do
  let n := 16
  let d : Std.Time.Millisecond.Offset := 50
  let hooks ← Runtime.Hooks.new
  let clock := Runtime.Clock.live hooks
  let e ← Sched.Executor.new LeanIn.Task.Item 256 1
  let ev ← IO.mkRef ([] : List String)
  let firstWakeOf (xs : List String) : Nat :=
    (xs.findIdx? (fun s => s.startsWith "wake:")).getD xs.length
  let overlaps (xs : List String) : Bool :=
    let w := firstWakeOf xs
    let startsBefore (ys : List String) : Nat := (ys.filter (fun s => s.startsWith "start:")).length
    w != 0 && startsBefore (xs.take w) == startsBefore xs
  let wakeCount (xs : List String) : Nat :=
    (xs.filter (fun s => s.startsWith "wake:")).length
  let sleeper : Nat → LeanIn.Task.Async Unit := fun i => do
    ev.modify (· ++ [s!"start:{i}"])
    Runtime.sleep clock d
    ev.modify (· ++ [s!"wake:{i}"])
  let t0 ← IO.monoNanosNow
  let _ ← Runtime.run e (do
    let hs ← (List.range n).mapM (fun i => LeanIn.Task.MonadAsync.spawn (sleeper i))
    let late ← LeanIn.Task.MonadAsync.spawn (ev.modify (· ++ ["ran:late"]))
    hs.forM (fun h => LeanIn.Task.MonadAwait.await h)
    LeanIn.Task.MonadAwait.await late)
  let t1 ← IO.monoNanosNow
  let events ← ev.get
  let firstWake := firstWakeOf events
  let overlap := overlaps events
  let lateBeforeWake := decide ((events.findIdx? (· == "ran:late")).getD events.length < firstWake)
  let wakes := wakeCount events
  -- the detectors' own controls: the same two readings on deliberately wrong orders
  let blockingOrder := (List.range 4).flatMap (fun i => [s!"start:{i}", s!"wake:{i}"])
  let blockingOrderOverlaps := overlaps blockingOrder
  let missingWakeWakes := wakeCount (events.filter (fun s => s != "wake:0"))
  let (hit, miss) ← Runtime.run e (do
    let hit ← Runtime.withTimeout clock 50 (Runtime.never : LeanIn.Task.Async Unit)
    let miss ← Runtime.withTimeout clock 200 (pure 7)
    return (hit, miss))
  -- The task layer's first-writer-wins law, and the timeout's own loser actually happening. The two writes are
  -- issued in order rather than raced, because which of two racing writers wins is a scheduling fact and this
  -- is a claim about the operation: the first value stays and the second is ignored. The `withTimeout` below
  -- is the integration half — the computation finishes, its 5 ms timer fires during the 40 ms after it, and
  -- the late write changes nothing. A `Join.resolve` in either position would raise out of the driver instead,
  -- so arriving at the print at all is part of the evidence.
  let (firstWins, lateTimerIgnored) ← Runtime.run e (do
    let cell ← LeanIn.Task.Join.new
    -- The writes are issued from this step, so each delivers on this step's own route.
    let push ← LeanIn.Task.Async.push
    LeanIn.Task.Join.resolveFirst cell push (some 1)
    LeanIn.Task.Join.resolveFirst cell push (some 2)
    let token ← (LeanIn.Task.Cancel.new : IO LeanIn.Task.Cancel)
    let first ← LeanIn.Task.Async.await (show LeanIn.Task.Task (Option Nat) from ⟨cell, token⟩)
    let late ← Runtime.withTimeout clock 5 (pure 7)
    Runtime.sleep clock 40
    return (first, late))
  -- Two baselines, and they are not the same kind of thing. The first is like-for-like: the same sixteen sleeps,
  -- *concurrently*, on the stock pool, one `IO.asTask` each — the shipped way to run something off the calling
  -- thread, and the number ours should be read against. The second issues the same waits one after another on
  -- one thread; it is not a baseline for "faster", it is what not overlapping them costs, and it belongs beside
  -- the first as the reason the first exists.
  let t2 ← IO.monoNanosNow
  let ts ← (List.range n).mapM (fun _ => IO.asTask (IO.sleep 50) _root_.Task.Priority.default)
  for t in ts do let _ ← IO.wait t
  let t3 ← IO.monoNanosNow
  let t4 ← IO.monoNanosNow
  for _ in List.range n do IO.sleep 50
  let t5 ← IO.monoNanosNow
  let hitStr := match hit with | none => "none" | some _ => "some"
  let missStr := match miss with | none => "none" | some v => s!"some:{v}"
  let firstStr := match firstWins with | none => "none" | some v => s!"some:{v}"
  let lateStr := match lateTimerIgnored with | none => "none" | some v => s!"some:{v}"
  IO.println s!"time|sleepers={n}|overlap={overlap}|lateBeforeWake={lateBeforeWake}|wakes={wakes}|timeoutHit={hitStr}|timeoutMiss={missStr}|firstWins={firstStr}|lateTimerIgnored={lateStr}|sleepUs={(t1 - t0) / 1000}"
  IO.println s!"timebase|stockPoolSleepUs={(t3 - t2) / 1000}|serialSleepUs={(t5 - t4) / 1000}"
  IO.println s!"timectl|blockingOrderOverlaps={blockingOrderOverlaps}|missingWakeWakes={missingWakeWakes}"
  -- The timeout's other half, read only through harness clocks; the record is the same one the dedicated
  -- `--runtime-time-loser` mode prints.
  timeoutLoserObservation
  return 0

/-- **The timeout's loser alone, with no live clock in the process.**

The dedicated mode for the timeout-cancellation behaviour check: it prints the `timeoutLoser|` record and runs
nothing else — no live clock, no real sleep, no socket, no metered W3 work — so a reading from it cannot be
attributed to the live half of `--runtime-time`.

Diagnostic: `lake exe controls --runtime-time-loser`. -/
def runtimeTimeLoser : IO UInt32 := do
  timeoutLoserObservation
  return 0

/-- **A deadline that fires from inside the computation it times out.**

The deadline is armed at virtual instant 10 before the child's first step is taken, and the child advances the
harness clock *while it is executing*: the fire runs on the child's own step, cancels the child's handle and
resolves the outer cell with `none`, and only then does the child return. Cancellation is therefore the first
writer to the child's handle, and the ordinary completion path that follows it is the second — so completing a
cancelled child must keep the first outcome, and the public timeout must return `none` rather than failing the
driver the run goes through.

`observeFailure` is the detector for a failure escaping the run. It is invoked on a deliberately thrown
`IO.Error` first, in the same invocation, so `failureDetectedWhenPresent=true` says the detector sees an escaped
failure at all; the overlap run is then read through that already-fired detector. The remaining fields are what
the child itself did: that it started, that advancing the clock from inside it actually fired the armed
deadline (`HarnessClock.advance` reports whether it had a pending timer to run), and that it returned.
`harnessAt=10` is the harness clock's own reading afterwards. The failure text is not classified, only its
presence.

Nothing here reads a live clock, sleeps for real or touches the loop: one carrier and one `HarnessClock`,
advanced by the child's own step.

Diagnostic: `lake exe controls`. -/
def controlTimeoutOverlap : IO Unit := do
  let observeFailure {α : Type} (act : IO α) : IO (Except IO.Error α) := do
    try
      return .ok (← act)
    catch e =>
      return .error e
  -- The detector's affirmative control, ahead of the reading it is a detector for.
  let sentinel := IO.userError "timeout overlap control: deliberate sentinel"
  let failureDetectedWhenPresent := match ← observeFailure (throw sentinel : IO Unit) with
    | .error _ => true
    | .ok _    => false
  let childStarted ← IO.mkRef false
  let timerAdvancedFromChild ← IO.mkRef false
  let childReturned ← IO.mkRef false
  let hc ← Runtime.HarnessClock.new
  let clock := Runtime.HarnessClock.clock hc
  let e ← Sched.Executor.new LeanIn.Task.Item 256 1
  let child : LeanIn.Task.Async Unit := do
    childStarted.set true
    -- Armed at instant 10 by the `withTimeout` below, and fired from inside the computation it times out.
    let advanced ← Runtime.HarnessClock.advance hc
    timerAdvancedFromChild.set advanced
    childReturned.set true
  let observed ← observeFailure (Runtime.runVirtual hc e (Runtime.withTimeout clock 10 child))
  let started ← childStarted.get
  let advancedFromChild ← timerAdvancedFromChild.get
  let returned ← childReturned.get
  let harnessAt ← Runtime.HarnessClock.now hc
  let outcomeStr := match observed with
    | .error _      => "error"
    | .ok none      => "none"
    | .ok (some ()) => "some"
  let record := s!"timeoutOverlap|childStarted={started}|timerAdvancedFromChild={advancedFromChild}|childReturned={returned}|harnessAt={harnessAt}|outcome={outcomeStr}|failureDetectedWhenPresent={failureDetectedWhenPresent}"
  IO.println record
  (← IO.getStdout).flush
  unless failureDetectedWhenPresent do
    throw (IO.userError s!"timeout overlap control: the failure detector missed a deliberately thrown error ({record})")
  unless started && advancedFromChild && returned && harnessAt == 10 do
    throw (IO.userError s!"timeout overlap control: the child did not advance the armed deadline from its own step and return at instant 10 ({record})")
  unless outcomeStr == "none" do
    throw (IO.userError s!"timeout overlap control: the deadline's first-wins outcome was not none ({record})")

/-- **The error channel, isolated.**

Two connects and nothing else: one to a port nothing listens on, which must return the failure *as a value*, and
one to a listener this program holds, which must return `ok` — the affirmative control for the first, in the same
run. The failure text is printed rather than classified, because the point of this mode is to be read.

**The listener is held in a reference that is used again after the connect, and that is the finding this mode
exists for.** A socket's descriptor dies with the *last use* of the Lean object that owns it, not at the end of
its scope: the first version read the address immediately before connecting and the listener was collected in
between, so the connect was reset by a socket that had been serving a moment earlier. Two of four runs also died
with SIGSEGV rather than a reset, which is the same hazard losing a race. Holding it in a reference whose own
last use is *after* the connect keeps both alive through it — which is also the rule a driver must follow for its
listener and for every connection it is serving.

Diagnostic: `lake exe controls --runtime-connect`. -/
def runtimeConnect : IO UInt32 := do
  let hooks ← Runtime.Hooks.new
  let e ← Sched.Executor.new LeanIn.Task.Item 256 1
  let refusedProg : LeanIn.Task.EAsync IO.Error Unit := do
    let _ ← Runtime.connect hooks (Runtime.loopback 1)
    pure ()
  let refused ← Runtime.run e refusedProg
  let refusedStr := match refused with | .ok _ => "ok" | .error err => s!"error:{err}"
  let l ← Runtime.Listener.bind (Runtime.loopback 0)
  let keep ← IO.mkRef l
  let acceptedProg : LeanIn.Task.EAsync IO.Error Unit := do
    let a ← monadLift (Runtime.Listener.sockName (← keep.get) : IO Std.Net.SocketAddress)
    let _ ← Runtime.connect hooks a
    pure ()
  let accepted ← Runtime.run e acceptedProg
  let stillBound ← Runtime.Listener.sockName (← keep.get)
  let acceptedStr := match accepted with | .ok _ => "ok" | .error err => s!"error:{err}"
  IO.println s!"connect|refused={refusedStr}|accepted={acceptedStr}|listener={stillBound}"
  return 0

/- **The cancellation: does a disconnect stop the work, and is a cancelled registration retired?**

SC11 drives this. One process, three actors on one executor: a **work** computation that counts and then parks on
a leaf; the **watcher**, which is the run's own computation — it accepts the first connection, awaits the peer
leaving, and in that same step reads the counter and cancels the work; and a **second connection**, served after
the cancellation and echoed.

The assertion is `counterAtCancel = counterFinal`: no step of a cancelled computation runs after the cancellation
was requested. It is the abort law rather than a timing claim — the counter is read in the cancelling step and
again after the run returns, so no clock enters it, and the leaf is resolved *after* the cancellation, so the
resumed step is one that would otherwise run.

`pendingAtCancel` and `pendingAfterCancel` are the registry's half. The work is parked when the cancellation
arrives, so a registration of its own is outstanding; once the computation it belongs to is gone it must not go on
being counted as work in flight. The second leaf is what makes that visible: it never completes, so a step of the
cancelled computation that ran would leave a registration behind for good.

`runUs` is printed and never asserted: the drain's latency is the poll interval, which is W7's absence rather than
a property of cancellation. -/
def runtimeCancel : IO UInt32 := do
  let hooks ← Runtime.Hooks.new
  let e ← Sched.Executor.new LeanIn.Task.Item 256 1
  let counter ← IO.mkRef (0 : Nat)
  -- The leaf the work parks on, resolved by the watcher *after* it cancels.
  let gate ← (IO.Promise.new : IO (IO.Promise (Except IO.Error Unit)))
  -- The leaf that never completes: the work reaches it only if a cancelled step ran, so its registration is what
  -- makes "not counted as in flight" observable rather than assumed.
  let dead ← (IO.Promise.new : IO (IO.Promise (Except IO.Error Unit)))
  let workRes ← IO.mkRef (none : Option (Except IO.Error Unit))
  let workTok ← IO.mkRef (none : Option LeanIn.Task.Cancel)
  let pendingAfterRef ← IO.mkRef (0 : Nat)
  let disconnectRef ← IO.mkRef "no"
  let secondRef ← IO.mkRef "no"
  let atCancelRef ← IO.mkRef (0 : Nat)
  let pendingAtRef ← IO.mkRef (0 : Nat)
  let doubleRef ← IO.mkRef "no"
  let l ← Runtime.Listener.bind (Runtime.loopback 0)
  let keep ← IO.mkRef l
  let addrRef ← IO.mkRef (none : Option Std.Net.SocketAddress)
  -- The new operation, measured: the fields are the plan's (`§5`), and every figure comes from a loop of its own
  -- inside one run, so nothing about the machine's state between runs enters them.
  --
  --   hooksAwaits / hooksCancelled  the registry's *live* registrations with N awaits in flight, and after those N
  --                                 are cancelled; registrySize is the same registry by list length, which the
  --                                 entries of a cancelled computation no longer appear in at all
  --   nsAwait                       spawn and await, without a cancellation
  --   nsCancel, and its three parts  the token set, the `resolveFirst`, and the retire, each measured alone
  --
  -- Two corrections are baked in, both found by measurement rather than by reading. A bare statement of a
  -- computation in this monad is not run, so the parkers get an explicit await before they are counted. And the
  -- promise they await is held by a reference this function reads *after* the run: a `Promise` whose last reference
  -- is dropped makes its task finish with `none`, so the first version of this bench was cancelling two hundred
  -- computations that had already completed, and counting a registry of dead entries as though it were in flight.
  -- That is the same lifetime rule SC9 and SC10 found for sockets, here for a promise.
  let benchN := 200
  let benchE ← Sched.Executor.new LeanIn.Task.Item 256 1
  let benchHooks ← Runtime.Hooks.new
  let never ← (IO.Promise.new : IO (IO.Promise (Except IO.Error Unit)))
  let hold ← IO.mkRef (some never)
  let benchProg : LeanIn.Task.EAsync IO.Error String := do
    let clock : IO Nat := IO.monoNanosNow
    let push ← LeanIn.Task.EAsync.ofAsync LeanIn.Task.Async.push
    let t0 ← monadLift clock
    for _ in List.range benchN do
      let h ← LeanIn.Task.MonadAsync.spawn (pure ())
      let _ ← LeanIn.Task.EAsync.ofAsync (LeanIn.Task.Async.await h)
      pure ()
    let t1 ← monadLift clock
    -- The loop cancels a computation that will never finish on its own, so the cancellation's `resolveFirst` is
    -- that cell's only writer. Cancelling one that *can* finish would make production without the gate — the state
    -- this mode must still be able to run, because the scenario's red lives there — resolve the same cell twice,
    -- which `Join.resolve` is loud about. Awaiting the handle here would be worse still: it would make the whole
    -- mode depend on the gate being present, which is what a red must not do.
    for _ in List.range benchN do
      let h ← LeanIn.Task.MonadAsync.spawn (LeanIn.Task.EAsync.ofAsync (Runtime.never : LeanIn.Task.Async Unit))
      monadLift (Runtime.cancel benchHooks h push (.error (.userError "bench")) : IO Unit)
      pure ()
    let t2 ← monadLift clock
    let ran ← monadLift (IO.mkRef (0 : Nat) : BaseIO (IO.Ref Nat))
    let parkers ← (List.range benchN).mapM (fun _ =>
      LeanIn.Task.MonadAsync.spawn (do
        monadLift (ran.modify (· + 1) : BaseIO Unit)
        Runtime.awaitPromiseE benchHooks never))
    let _ ← LeanIn.Task.EAsync.ofAsync (Runtime.sleep (Runtime.Clock.live benchHooks) 20)
    let awaits ← monadLift (Runtime.pending benchHooks : IO Nat)
    let size ← monadLift (Runtime.Hooks.size benchHooks : IO Nat)
    let ranN ← monadLift (ran.get : IO Nat)
    -- The parts of a cancellation, each alone. The retire runs over the registry as it stands — the N parkers'
    -- entries — which is the shape a cancellation meets: one scan of the list it is about to shorten.
    let one ← LeanIn.Task.MonadAsync.spawn (pure ())
    let t3 ← monadLift clock
    for _ in List.range benchN do monadLift (one.token.set : BaseIO Unit)
    let t4 ← monadLift clock
    let cell ← monadLift (LeanIn.Task.Join.new : IO (LeanIn.Task.Join Unit))
    for _ in List.range benchN do monadLift (LeanIn.Task.Join.resolveFirst cell push () : IO Unit)
    let t5 ← monadLift clock
    for _ in List.range benchN do monadLift (Runtime.Hooks.retire benchHooks : IO Unit)
    let t6 ← monadLift clock
    for h in parkers do
      let push2 ← LeanIn.Task.EAsync.ofAsync LeanIn.Task.Async.push
      monadLift (Runtime.cancel benchHooks h push2 (.error (.userError "bench")) : IO Unit)
    let cancelled ← monadLift (Runtime.pending benchHooks : IO Nat)
    return s!"hooksAwaits={awaits}|hooksCancelled={cancelled}|registrySize={size}|nsAwait={(t1 - t0) / benchN}|nsCancel={(t2 - t1) / benchN}|nsCancelFlag={(t4 - t3) / benchN}|nsCancelResolve={(t5 - t4) / benchN}|nsCancelRetire={(t6 - t5) / benchN}|parkersRan={ranN}"
  let benchOut ← Runtime.run benchE benchProg
  let benchStr := match benchOut with
    | .ok s => s
    | .error _ => "failed"
  -- A use after the run, so the promise outlives the parkers that await it.
  let _held ← hold.get
  IO.println s!"cancelbench|{benchStr}"
  let runAt ← IO.mkRef (0 : Nat)
  runAt.set (← IO.monoNanosNow)
  let payload : ByteArray := "cancel me".toUTF8
  let program : LeanIn.Task.EAsync IO.Error Unit := do
    let a ← monadLift (Runtime.Listener.sockName (← keep.get) : IO Std.Net.SocketAddress)
    addrRef.set (some a)
    let work : LeanIn.Task.EAsync IO.Error Unit := do
      counter.modify (· + 1)
      let _ ← Runtime.awaitPromiseE hooks gate
      counter.modify (· + 1)
      let _ ← Runtime.awaitPromiseE hooks dead
      pure ()
    let handle ← LeanIn.Task.MonadAsync.spawn work
    workTok.set (some handle.token)
    let c1 ← Runtime.Listener.accept (← keep.get) hooks
    -- The first connection is served by watching its read side: the peer closing *is* the disconnect, and no
    -- clock is involved. The work was spawned before this step, so it is parked by the time the peer leaves.
    let arrived ← Runtime.Conn.recv c1 hooks
    disconnectRef.set (if arrived == none then "yes" else "no")
    let atCancel ← counter.get
    let tok ← workTok.get
    let ofWork (k : LeanIn.Task.Cancel) : LeanIn.Task.EAsync IO.Error Nat :=
      monadLift (Runtime.pendingFor hooks k : IO Nat)
    let pendingAt ← match tok with
      | some tk => ofWork tk
      | none    => pure 0
    atCancelRef.set atCancel
    pendingAtRef.set pendingAt
    -- The cancellation's route is read here, in the step that makes the call: a route fetched earlier would
    -- be the route of a worker this step may not be running on.
    let push ← LeanIn.Task.EAsync.ofAsync LeanIn.Task.Async.push
    monadLift (Runtime.cancel hooks handle push (.error (.userError "canceled")) : IO Unit)
    let afterCancel ← match tok with
      | some tk => ofWork tk
      | none    => pure 0
    pendingAfterRef.set afterCancel
    let ok : Except IO.Error Unit := .ok ()
    monadLift (IO.Promise.resolve ok gate : BaseIO Unit)
    let secondTry ← try
        let push2 ← LeanIn.Task.EAsync.ofAsync LeanIn.Task.Async.push
        monadLift (Runtime.cancel hooks handle push2 (.error (.userError "canceled")) : IO Unit)
        pure "ok"
      catch _ => pure "raised"
    doubleRef.set secondTry
    -- The second connection: accepted and echoed after the cancellation, which is W5's second clause.
    let c2 ← Runtime.Listener.accept (← keep.get) hooks
    match ← Runtime.Conn.recv c2 hooks with
    | some bs =>
      Runtime.Conn.send c2 hooks bs
      -- The payload is compared rather than assumed: "served" here means the echo came back, not only that the
      -- connection was accepted.
      secondRef.set (if bs == payload then "yes" else "no")
    | none => secondRef.set "no"
    let res ← LeanIn.Task.EAsync.ofAsync (LeanIn.Task.Async.await handle)
    workRes.set (some res)
    pure ()
  let server ← IO.asTask (Runtime.run e program) _root_.Task.Priority.dedicated
  let addr ← do
    let mut a : Option Std.Net.SocketAddress := none
    while a.isNone do a ← addrRef.get
    pure (a.getD (Runtime.loopback 0))
  let echoed ← Std.Async.Async.block do
    let c ← Std.Async.TCP.Socket.Client.mk
    c.connect addr
    c.shutdown
    let c2 ← Std.Async.TCP.Socket.Client.mk
    c2.connect addr
    c2.send payload
    let got ← c2.recv? 65536
    c2.shutdown
    return got
  let outcome ← IO.wait server
  let returnedAt ← IO.monoNanosNow
  let counterFinal ← counter.get
  let _stillBound ← Runtime.Listener.sockName (← keep.get)
  let cancelledStr :=
    match ← workRes.get with
    | some (.error _) => "canceled"
    | some (.ok _)    => "ok"
    | none            => "none"
  let _echoed ← IO.mkRef echoed
  match outcome with
  | .error err        => IO.println s!"cancel|failed={err}"; return 1
  | .ok (.error err)  => IO.println s!"cancel|failed={err}"; return 1
  | .ok (.ok ()) =>
    IO.println s!"cancel|disconnect={← disconnectRef.get}|second={← secondRef.get}|counterAtCancel={← atCancelRef.get}|counterFinal={counterFinal}|pendingAtCancel={← pendingAtRef.get}|pendingAfterCancel={← pendingAfterRef.get}|cancelled={cancelledStr}|doubleCancel={← doubleRef.get}|runUs={(returnedAt - (← runAt.get)) / 1000}"
    return 0

/- **The drain: does a stop, with a connection in flight, return the loop's own value?**

It began as the first rung of a ladder — the loop with no connections at all, so that `tryAccept` returns `none`,
the poll sleeps, and the stop flag is the only thing that can end it. That rung found a real bug: the run came
back as `error: Runtime.run: the driver stopped before the computation finished`, because `blockOn` ended the
driver as soon as the pool was empty and the executor was stopping, and a stopped executor still holds work as
continuations registered on leaves — those are not in the pool by construction, because an awaited leaf yields
and queues nothing. Fixed in `blockOn`, it now reads the server-shaped half too: the served connection stops the
executor from *inside* the body, so a connection is in flight when the stop arrives by construction rather than by
a race with the accept, and the record reads `served=1 echoed=yes inFlightAfter=0 pendingHooks=0` — the
connection's own echo coming back after the stop, an empty pool, and no leaf registration left outstanding.

`drainUs` is recorded and never asserted on: the poll interval bounds the drain, and that interval is W7's
absence showing through rather than a property of this mode. A diagnostic, not a scenario — SC10 is the scenario,
and this mode is the reading its control is built on. -/
def runtimeDrain : IO UInt32 := do
  let hooks ← Runtime.Hooks.new
  let l ← Runtime.Listener.bind (Runtime.loopback 0)
  let keep ← IO.mkRef l
  let e ← Sched.Executor.new LeanIn.Task.Item 256 1
  let served ← IO.mkRef (0 : Nat)
  let addrRef ← IO.mkRef (none : Option Std.Net.SocketAddress)
  let stopAt ← IO.mkRef (0 : Nat)
  let server ← IO.asTask (Runtime.run e (do
    let a ← monadLift (Runtime.Listener.sockName (← keep.get) : IO Std.Net.SocketAddress)
    addrRef.set (some a)
    Runtime.serveUntilStopped hooks e (← keep.get) 1 (fun c => do
      served.modify (· + 1)
      -- The connection stops the server, and it does so *here*, inside the body being served. That removes the
      -- race the first version had: a client that sends and then stops can stop before the accept happens, and
      -- then the loop drains an empty list while the connection waits in the backlog for an accept that never
      -- comes — a hang, produced twice. Stopping from inside the served connection makes "a connection is in
      -- flight when the stop arrives" true by construction rather than by hope.
      let now ← monadLift (IO.monoNanosNow : IO Nat)
      stopAt.set now
      monadLift (e.stop : IO Unit)
      echoAccepted hooks c) [])) _root_.Task.Priority.dedicated
  let payload : ByteArray := "drain me".toUTF8
  let addr ← do
    let mut a : Option Std.Net.SocketAddress := none
    while a.isNone do a ← addrRef.get
    pure (a.getD (Runtime.loopback 0))
  let echoed ← Std.Async.Async.block do
    let c ← Std.Async.TCP.Socket.Client.mk
    c.connect addr
    c.send payload
    let got ← c.recv? 65536
    c.shutdown
    return got
  let outcome ← IO.wait server
  -- A use *after* the drain, so the listener outlives the loop that used it. This is the rule `--runtime-connect`
  -- found: a socket's descriptor dies with the last use of the Lean object owning it, and the loop's final
  -- `tryAccept` is not the end of the run — the drain waits on connections after it, and the reset that produced
  -- the first version of this mode was that socket going away mid-drain.
  let stillBound ← Runtime.Listener.sockName (← keep.get)
  let returnedAt ← IO.monoNanosNow
  let (inFlightAfter, _) ← e.observe
  let pendingAfter ← Runtime.pending hooks
  let echoedStr := if echoed == some payload then "yes" else "no"
  let servedStr := toString (← served.get)
  match outcome with
  | .error err => IO.println s!"drain|failed={err}"; return 1
  | .ok (.error err) => IO.println s!"drain|failed={err}"; return 1
  | .ok (.ok ()) =>
    IO.println s!"drain|served={servedStr}|echoed={echoedStr}|inFlightAfter={inFlightAfter}|pendingHooks={pendingAfter}|listener={stillBound}|drainUs={(returnedAt - (← stopAt.get)) / 1000}"
    return 0

/-- **SC12 — blocking jobs run off the carrier, on a bounded pool, without stalling the executor.**

Four blocking jobs go through the runtime's blocking pool, each recording the thread it ran on, while a
heartbeat of cheap carrier steps keeps the executor busy and reads the runtime's outstanding-registration
count. One record reads: the jobs ran on threads other than `carrier` (2), four jobs shared at most
`poolWorkers` threads, so it is a pool and not a thread per job (3), a carrier step fell strictly between the
first job's start and its completion (4), every completion resumed on the carrier (5), the stock-priority task
finished before the jobs did (6), the accounting reader saw every job while they were outstanding (7) and none
after the pool was shut down (8), and every worker exited (9). Every identity is `IO.getTID` read where it
happened and every order is the actors' own annotation order; `runUs` is printed and never asserted on.

The mode also prints the readings of its own detectors on a `blockctl|` line: the distinct-thread detector
counts two on two distinct tids and one on a repeat, the order detector rejects the blocking-shaped order and
accepts an interleaved one, and the stock guard rejects a record that says the stock pool was taken.

Diagnostic: `lake exe controls --runtime-blocking`. -/
def runtimeBlocking : IO UInt32 := do
  let hooks ← Runtime.Hooks.new
  let e ← Sched.Executor.new LeanIn.Task.Item 256 1
  let pool ← Runtime.BlockingPool.new 2
  let carrier ← IO.getTID
  let jobs := 4
  let log ← IO.mkRef ([] : List String)
  let jobTids ← IO.mkRef ([] : List UInt64)
  let resumeTids ← IO.mkRef ([] : List UInt64)
  let pendingPeak ← IO.mkRef (0 : Nat)
  -- Every actor records where it ran and what it did, at the point it happened. Each job writes its own
  -- thread into its own cell, so the identities are collected in job order rather than in completion order.
  let jobBody (i : Nat) (cell : IO.Ref (Option UInt64)) : IO Unit := do
    log.modify (fun l => l ++ [s!"job{i}-start"])
    cell.set (some (← IO.getTID))
    IO.sleep (25 : UInt32)
    log.modify (fun l => l ++ [s!"job{i}-done"])
  -- The heartbeat is *steps*, not one long step: it appends `hb` and reads the registry, then yields to a
  -- trivial child and awaits it, so each iteration is another carrier step.
  let rec heartbeat : Nat → LeanIn.Task.Async Unit
    | 0 => pure ()
    | n + 1 => do
        let p ← monadLift (Runtime.pending hooks)
        monadLift (pendingPeak.modify (fun m => max m p) : IO Unit)
        log.modify (fun l => l ++ ["hb"])
        let h ← LeanIn.Task.Async.spawn (pure () : LeanIn.Task.Async Unit)
        LeanIn.Task.Async.await h
        heartbeat n
  let carrierBetween (events : List String) : Bool :=
    match events.findIdx? (· == "job0-start"), events.findIdx? (· == "job0-done") with
    | some s, some d => (events.drop (s + 1)).take (d - (s + 1)) |>.any (· == "hb")
    | _, _ => false
  let stockGuard : String → Bool := fun v => v == "yes"
  let runAt ← IO.monoNanosNow
  let _ ← Runtime.run e (do
    -- 1. the four blocking jobs
    let hs ← (List.range jobs).mapM (fun i => do
      let cell ← monadLift (IO.mkRef (none : Option UInt64))
      let h ← LeanIn.Task.Async.spawn (Runtime.spawnBlocking pool hooks (jobBody i cell))
      pure (cell, h))
    -- 2. the heartbeat
    let hb ← LeanIn.Task.Async.spawn (heartbeat 200)
    -- 3. one stock default-priority task, awaited
    let stock ← monadLift (IO.asTask (log.modify (fun l => l ++ ["stock"])) _root_.Task.Priority.default)
    let _ ← monadLift (IO.wait stock)
    -- 4. await every job, recording the thread its continuation resumed on
    hs.forM (fun (_, h) => do
      LeanIn.Task.Async.await h
      let tid ← monadLift (IO.getTID : IO UInt64)
      monadLift (resumeTids.modify (fun l => l ++ [tid]) : IO Unit))
    -- the job identities, read in job order
    hs.forM (fun (cell, _) => do
      match ← monadLift (cell.get : IO (Option UInt64)) with
      | some t => monadLift (jobTids.modify (fun l => l ++ [t]) : IO Unit)
      | none   => pure ())
    -- 5. the heartbeat, then the pool's own shutdown/drain
    LeanIn.Task.Async.await hb
    monadLift (Runtime.BlockingPool.shutdownAndWait pool)
    pure ())
  let returnedAt ← IO.monoNanosNow
  let events ← log.get
  let tids ← jobTids.get
  let rtids ← resumeTids.get
  let peak ← pendingPeak.get
  let pendingAfter ← Runtime.pending hooks
  let exited ← pool.state.atomically do return (← get).exited
  let lastDone := (events.findIdx? (· == s!"job{jobs - 1}-done")).getD 0
  let stockBefore := decide ((events.findIdx? (· == "stock")).getD events.length < lastDone)
  let during := if carrierBetween events then "yes" else "no"
  let stockBeforeStr := if stockBefore then "yes" else "no"
  let tidsStr := String.intercalate "," (tids.map toString)
  let rtidsStr := String.intercalate "," (rtids.map toString)
  IO.println s!"block|jobs={jobs}|carrier={carrier}|jobTids=[{tidsStr}]|poolWorkers={pool.workers}|carrierDuringFirstJob={during}|resumeTids=[{rtidsStr}]|stockBeforeJobs={stockBeforeStr}|pendingPeak={peak}|pendingAfter={pendingAfter}|workersExited={exited}|runUs={(returnedAt - runAt) / 1000}"
  IO.println s!"blockctl|distinctTwo={(distinctOf [0, 1]).length}|distinctRepeat={(distinctOf [7, 7]).length}|orderBlocking={carrierBetween ["job0-start", "job0-done", "hb"]}|orderInterleaved={carrierBetween ["job0-start", "hb", "job0-done"]}|stockGuardYes={if stockGuard "yes" then "accepted" else "rejected"}|stockGuardNo={if stockGuard "no" then "accepted" else "rejected"}"
  return 0

/- **SC13 — async synchronisation: a mutex, a semaphore and a bounded channel on one carrier.**

Three computations share an async mutex across awaits and their sections do not overlap; an unrelated
step falls strictly inside the first section; a flood of sends against a bounded channel holds with an
exact accepted/rejected count beside a channel with room; a semaphore's permits are counted exactly;
and each primitive's cancellation law is read from a non-parking probe — a cancelled lock waiter is
not granted the lock, a cancelled receiver consumes no message, a cancelled sender consumes no slot.
Every comparison is a named field of the mode's one `sync|` record, and every event in its `order`
field was appended by the actor that caused it, where it happened. Nothing reads a queue or a slot:
the boundary is the executable's stdout. The mode also prints its own checker's readings on a
well-formed record and on near misses (`syncctl|`), and three measurement lines that are printed and never
asserted: `syncbench|`, the per-operation costs, `waiterbench|`, the cost of parking a large number of
waiters on one primitive, and `chanunit|`, the served channel operation decomposed part by part. -/

/-- The `sync|` record's fields, in the order the mode prints them. -/
def syncFields : List String :=
  ["cap", "order", "aResult", "bResult", "sent", "tryAccepted", "tryRejected", "parkedDelivered",
   "controlAccepted", "controlRejected", "semAccepted", "semRejected", "semAfterRelease",
   "cancelLockAcquired", "cancelRecvValue", "cancelSendGhost", "cancelSendAccepted", "runUs"]

/-- One field of a `key=value|…` record: its value when the key appears exactly once and nonempty,
and `none` when it is absent, repeated or empty — so a value is never bound from a neighbour. -/
def syncField (rec key : String) : Option String :=
  let vals := (rec.splitOn "|").filterMap (fun tok =>
    match tok.splitOn "=" with
    | [k, v] => if k == key then some v else none
    | _      => none)
  match vals with
  | [v] => if v == "" then none else some v
  | _   => none

/-- A nonempty natural field. -/
def syncNat (rec key : String) : Option Nat :=
  (syncField rec key).bind String.toNat?

/-- The record's fields are exactly `syncFields`, in order, each nonempty. -/
def syncShaped (rec : String) : Bool :=
  let toks := rec.splitOn "|"
  toks.length == syncFields.length &&
  (toks.zip syncFields).all (fun (tok, key) =>
    match tok.splitOn "=" with
    | [k, v] => k == key && v != ""
    | _      => false)

/-- The `order` stream: exactly the six events `a-enter`, `a-exit`, `b-enter`, `b-exit`, `u`, `u`,
once each; the two sections do not interleave; and a `u` falls strictly inside the first section. The
relations are read from the events' positions, never from a stream compared to a fixed string. -/
def syncOrderOk (events : List String) : Bool :=
  events.length == 6 &&
  events.count "u" == 2 && events.count "a-enter" == 1 && events.count "a-exit" == 1 &&
  events.count "b-enter" == 1 && events.count "b-exit" == 1 &&
  events.all (fun e => e == "u" || e == "a-enter" || e == "a-exit" || e == "b-enter" || e == "b-exit") &&
  (match events.findIdx? (· == "a-enter"), events.findIdx? (· == "a-exit"),
         events.findIdx? (· == "b-enter"), events.findIdx? (· == "b-exit") with
   | some ai, some ax, some bi, some bx =>
       ai < ax && bi < bx && (ax < bi || bx < ai) &&
       (let first := if ai < bi then (ai, ax) else (bi, bx)
        ((List.range events.length).filter (fun i => events.getD i "" == "u")).any
          (fun i => first.1 < i && i < first.2))
   | _, _, _, _ => false)

/-- The record satisfies every binding of the contract: both holders' values are distinct and
present, the bound holds exactly with its affirmative control, every parked send is delivered, the
semaphore's count is exact, and the three cancellation probes read the expected fields. -/
def syncOk (rec : String) : Bool :=
  syncShaped rec &&
  (match syncField rec "order" with
   | some o => syncOrderOk (o.splitOn ",")
   | none   => false) &&
  (match syncField rec "aResult", syncField rec "bResult" with
   | some a, some b => a != b
   | _, _           => false) &&
  (match syncNat rec "cap", syncNat rec "sent", syncNat rec "tryAccepted", syncNat rec "tryRejected",
         syncNat rec "parkedDelivered", syncNat rec "controlAccepted", syncNat rec "controlRejected",
         syncNat rec "semAccepted" with
   | some cap, some sent, some ta, some tr, some pd, some ca, some cr, some sa =>
       sent == cap + 1 && ta == cap && tr == 1 && pd == sent && ca == sent && cr == 0 && sa == 2
   | _, _, _, _, _, _, _, _ => false) &&
  syncField rec "semRejected" == some "no" &&
  syncField rec "semAfterRelease" == some "yes" &&
  syncField rec "cancelLockAcquired" == some "yes" &&
  syncField rec "cancelRecvValue" == some "present" &&
  syncField rec "cancelSendGhost" == some "absent" &&
  syncField rec "cancelSendAccepted" == some "yes"

/-- The checker's verdict as one word, so a reading is `accepted` or `rejected` and nothing else. -/
def syncReading (b : Bool) : String := if b then "accepted" else "rejected"

/-- A well-formed `sync|` record, built from the record syntax and the expected values rather than
from the mode's output, so the checker's controls cannot agree with the mode by construction. -/
def syncGoodRec : String :=
  "cap=2|order=a-enter,u,a-exit,b-enter,u,b-exit|aResult=7|bResult=9|sent=3|tryAccepted=2|tryRejected=1|parkedDelivered=3|controlAccepted=3|controlRejected=0|semAccepted=2|semRejected=no|semAfterRelease=yes|cancelLockAcquired=yes|cancelRecvValue=present|cancelSendGhost=absent|cancelSendAccepted=yes|runUs=0"

def syncNearOrderOverlap : String :=
  syncGoodRec.replace "order=a-enter,u,a-exit,b-enter,u,b-exit" "order=a-enter,b-enter,a-exit,b-exit,u,u"

def syncNearUnrelated : String :=
  syncGoodRec.replace "order=a-enter,u,a-exit,b-enter,u,b-exit" "order=a-enter,a-exit,u,u,b-enter,b-exit"

def syncNearCount : String := syncGoodRec.replace "tryAccepted=2" "tryAccepted=1"
def syncNearControl : String := syncGoodRec.replace "controlRejected=0" "controlRejected=1"
def syncNearSemCount : String := syncGoodRec.replace "semAccepted=2" "semAccepted=1"
def syncNearSemAfter : String := syncGoodRec.replace "semAfterRelease=yes" "semAfterRelease=no"
def syncNearLock : String := syncGoodRec.replace "cancelLockAcquired=yes" "cancelLockAcquired=no"
def syncNearRecv : String := syncGoodRec.replace "cancelRecvValue=present" "cancelRecvValue=lost"
def syncNearSend : String := syncGoodRec.replace "cancelSendGhost=absent" "cancelSendGhost=present"

def syncCtlPair (name near : String) : String :=
  s!"{name}Near={syncReading (syncOk near)}|{name}Good={syncReading (syncOk syncGoodRec)}"

/-- The mode's own checker readings, on a record whose named relation is broken and on a well-formed
record: each pair is `rejected` then `accepted` when the checker discriminates. -/
def syncCtlLine : String :=
  "syncctl|" ++ String.intercalate "|" [
    syncCtlPair "orderOverlap" syncNearOrderOverlap,
    syncCtlPair "unrelatedInside" syncNearUnrelated,
    syncCtlPair "countExact" syncNearCount,
    syncCtlPair "controlShows" syncNearControl,
    syncCtlPair "semCount" syncNearSemCount,
    syncCtlPair "semAfter" syncNearSemAfter,
    syncCtlPair "lockProbe" syncNearLock,
    syncCtlPair "recvProbe" syncNearRecv,
    syncCtlPair "sendProbe" syncNearSend]

/-- `n` lock/unlock pairs on one mutex, as one computation. A release delivers the waiters it wakes, so it
takes the releasing step's own route. -/
def syncLockPairs (m : LeanIn.Task.Sync.Mutex) : Nat → LeanIn.Task.Async Unit
  | 0     => pure ()
  | n + 1 => do
      LeanIn.Task.Sync.Mutex.lock m
      let push ← LeanIn.Task.Async.push
      LeanIn.Task.Sync.Mutex.unlock m push
      syncLockPairs m n

/-- Yield the rest of this computation as a fresh step on the same carrier, so another computation's step can
run at the boundary. The task layer exposes no primitive for this, so it is spelled here as `ctx.resume` of a
continuation: the item goes into this worker's own slot and this worker fires it, so the context it carries is
already the firing one. -/
def syncYield : LeanIn.Task.Async Unit := ⟨fun k ctx => do
  ctx.resume (LeanIn.Task.Item.ofDeferred ctx (k ()))⟩

/-- `n` lock/unlock pairs where each pair **holds the permit across a yield**, so two computations running this
interleave at the mutex: one takes the permit, yields, and the other's non-parking `tryLock` **finds it held** —
which is the observation recorded in `held`, and the difference between real contention and two chains that each
run straight through — before parking via `lock` until the first releases. The acquisition is the probe: a
`tryLock` that succeeds takes the permit exactly as `lock` would, and only a `tryLock` that fails (the permit
gone, i.e. held by the sibling across its yield) records `held` and then parks. This — not two spawned chains
that each run straight through — is the case an async mutex exists for. -/
def syncLockPairsYielding (m : LeanIn.Task.Sync.Mutex) (held : IO.Ref Bool) : Nat → LeanIn.Task.Async Unit
  | 0     => pure ()
  | n + 1 => do
      let got ← LeanIn.Task.Sync.Mutex.tryLock m
      if got then
        pure ()
      else do
        held.set true
        LeanIn.Task.Sync.Mutex.lock m
      syncYield
      let push ← LeanIn.Task.Async.push
      LeanIn.Task.Sync.Mutex.unlock m push
      syncLockPairsYielding m held n

/-- `n` acquires on one semaphore, as one computation. -/
def syncSemAcquires (s : LeanIn.Task.Sync.Semaphore) : Nat → LeanIn.Task.Async Unit
  | 0     => pure ()
  | n + 1 => do
      LeanIn.Task.Sync.Semaphore.acquire s
      syncSemAcquires s n

/-- `n` releases on one semaphore, as one computation. -/
def syncSemReleases (s : LeanIn.Task.Sync.Semaphore) : Nat → LeanIn.Task.Async Unit
  | 0     => pure ()
  | n + 1 => do
      let push ← LeanIn.Task.Async.push
      LeanIn.Task.Sync.Semaphore.release s push
      syncSemReleases s n

/-- The `syncbench|` rows: per-op nanoseconds for the uncontended and contended lock, a release that
wakes `16` parked waiters, the semaphore's acquire and release, and the bounded channel's per-message
cost beside the same message count through the stock channel in one run. Printed, never asserted.

The contended row runs two computations that each hold the permit across a yield, so they genuinely
interleave at the mutex — one parks while the other holds it — rather than each running its whole chain inside
one step. `heldAcrossYield` prints whether that interleaving was **observed**: a non-parking `tryLock` inside
the yielding chains found the permit already held by the sibling while this computation expected to acquire it.
It prints `no` rather than being omitted, so a construction that failed to interleave shows as `no` instead of
going silent. -/
def syncBench : IO String := do
  let n := 2000
  let timeRun (prog : LeanIn.Task.Async Unit) : IO Nat := do
    let e ← Sched.Executor.new LeanIn.Task.Item 256 1
    let t0 ← IO.monoNanosNow
    let _ ← Runtime.run e prog
    let t1 ← IO.monoNanosNow
    return t1 - t0
  let m1 ← LeanIn.Task.Sync.Mutex.new
  let lockNs ← timeRun (syncLockPairs m1 n)
  let m2 ← LeanIn.Task.Sync.Mutex.new
  let heldRef ← IO.mkRef false
  let contNs ← timeRun (do
    let h1 ← LeanIn.Task.Async.spawn (syncLockPairsYielding m2 heldRef (n / 2))
    let h2 ← LeanIn.Task.Async.spawn (syncLockPairsYielding m2 heldRef (n / 2))
    let _ ← LeanIn.Task.Async.await h1
    let _ ← LeanIn.Task.Async.await h2)
  let heldAcross ← heldRef.get
  let heldStr := if heldAcross then "yes" else "no"
  let s1 ← LeanIn.Task.Sync.Semaphore.new n
  let semAcqNs ← timeRun (syncSemAcquires s1 n)
  let s2 ← LeanIn.Task.Sync.Semaphore.new n
  let semRelNs ← timeRun (syncSemReleases s2 n)
  let w := 16
  let s3 ← LeanIn.Task.Sync.Semaphore.new 0
  let relNs ← timeRun (do
    let push ← LeanIn.Task.Async.push
    for _ in List.range w do
      let _ ← LeanIn.Task.Async.spawn (LeanIn.Task.Sync.Semaphore.acquire s3)
      pure ()
    LeanIn.Task.Sync.Semaphore.release s3 push)
  let cap := n
  let c1 ← LeanIn.Task.Sync.Channel.new Nat cap
  let chanOursNs ← timeRun (do
    for i in List.range n do LeanIn.Task.Sync.Channel.send c1 i
    for _ in List.range n do
      let _ ← LeanIn.Task.Sync.Channel.recv c1
      pure ())
  let c2 ← Std.Channel.new (some n)
  let scT0 ← IO.monoNanosNow
  for i in List.range n do
    let _ ← IO.wait (← Std.Channel.send c2 i)
    let _ ← IO.wait (← Std.Channel.recv c2)
  let scT1 ← IO.monoNanosNow
  let ours := max 1 (chanOursNs / n)
  let stdNs := (scT1 - scT0) / n
  return s!"nsLockUncontended={lockNs / n}|nsLockContended={contNs / n}|heldAcrossYield={heldStr}|nsReleaseWakeW={relNs / w}|nsSemAcquire={semAcqNs / n}|nsSemRelease={semRelNs / n}|nsChanOurs={ours}|nsChanStd={stdNs}|chanRatioPct={stdNs * 100 / ours}"

/-- **Park `n` computations on one operation and time the registration path.**

Each child increments a shared counter as its first action and the child that reaches `n` resolves a
promise the parent waits on, so the parent resumes only after the last child's parking step has run to its
end on the single carrier — a child that increments and then parks does both inside one step, so the
`n`th increment is the last park. The window opens before the child spawns, so the spawn-only control
subtracted in `waiterBench` is like-for-like.

The `n` handles are returned so the caller can cancel the parked waiters: cancelling sets each token and
resolves each cell, so a run whose children never get a permit still ends without waking them. Printed,
never asserted. -/
def parkTimed (hooks : Runtime.Hooks) (n : Nat) (park : LeanIn.Task.Async Unit) :
    LeanIn.Task.Async (Nat × List (LeanIn.Task.Task Unit)) := do
  let counter ← IO.mkRef (0 : Nat)
  let p ← (IO.Promise.new : IO (IO.Promise (Except IO.Error Unit)))
  let t0 ← IO.monoNanosNow
  let hs ← (List.range n).mapM fun _ => LeanIn.Task.Async.spawn (do
    let c ← counter.get
    counter.set (c + 1)
    if c + 1 == n then p.resolve (Except.ok ())
    park)
  let _ ← Runtime.awaitPromiseE hooks p
  let t1 ← IO.monoNanosNow
  return (t1 - t0, hs)

/-- Run `parkTimed` for `n` on one freshly-built executor, cancel the parked waiters so the run can end,
and return the nanoseconds the window took. -/
def parkRun (n : Nat) (park : LeanIn.Task.Async Unit) : IO Nat := do
  let e ← Sched.Executor.new LeanIn.Task.Item 256 1
  let hooks ← Runtime.Hooks.new
  Runtime.run e (do
    let (ns, hs) ← parkTimed hooks n park
    let push ← LeanIn.Task.Async.push
    for h in hs do Runtime.cancel hooks h push ()
    for h in hs do let _ ← LeanIn.Task.Async.await h; pure ()
    pure ns)

/-- **The raw list costs the registration path is built on**, in the same window: building an `n`-element
list by `acc ++ [x]` and by `x :: acc`. The lengths are summed and printed as a checksum so neither build
can be elided. -/
def nativeListNs (n : Nat) : IO (Nat × Nat × Nat) := do
  let t0 ← IO.monoNanosNow
  let app := (List.range n).foldl (fun acc x => acc ++ [x]) []
  let t1 ← IO.monoNanosNow
  let cons := (List.range n).foldl (fun acc x => x :: acc) []
  let t2 ← IO.monoNanosNow
  return (t1 - t0, t2 - t1, app.length + cons.length)

/-- The machine's 1-minute load average, so a reading can be set beside the load it was taken under. -/
def loadAvg : IO String := do
  try
    let s ← IO.FS.readFile "/proc/loadavg"
    return (s.splitOn " ").headD "?"
  catch _ => return "?"

/-- **The push for a call whose waiter list is empty by construction.** The benches below send into a channel
nobody is parked on and receive from one with no parked sender, so no delivery happens and the call has no route
to name: this says that, rather than borrowing a route that would misdescribe the call. It is never called. -/
def noWaiterPush : LeanIn.Task.Item → BaseIO Unit := fun _ => pure ()

/-- **The `waiterbench|` rows: parking a large number of waiters.**

One line per size `n`: the nanoseconds to park `n` computations on the semaphore's `acquire`, on a full
channel's `send` and on an empty channel's `recv`, total and per waiter; the same invocation's spawn-only
control, total and per waiter; the registration left after the control is subtracted, per waiter — the
figure that shows whether the registration path still grows with the list — and the raw `++`/cons list
costs and the load average of the same window. Printed, never asserted (§1: a timing assertion is a flake
with a schedule). -/
def waiterBench : IO Unit := do
  let sizes := [256, 512, 1024, 2048, 4096]
  let load ← loadAvg
  for n in sizes do
    let ctlNs ← parkRun n (pure ())
    let s ← LeanIn.Task.Sync.Semaphore.new 0
    let semNs ← parkRun n (LeanIn.Task.Sync.Semaphore.acquire s)
    let cs ← LeanIn.Task.Sync.Channel.new Unit 1
    let _ ← LeanIn.Task.Sync.Channel.trySend cs () noWaiterPush
    let sendNs ← parkRun n (LeanIn.Task.Sync.Channel.send cs ())
    let cr ← LeanIn.Task.Sync.Channel.new Unit 1
    let recvNs ← parkRun n (LeanIn.Task.Sync.Channel.recv cr)
    let (appNs, consNs, chk) ← nativeListNs n
    let perNs (x : Nat) : Nat := x / n
    let regNs (x : Nat) : Nat := (x - ctlNs) / n
    IO.println s!"waiterbench|n={n}|semNs={semNs}|semPerWaiter={perNs semNs}|semRegPerWaiter={regNs semNs}|sendNs={sendNs}|sendPerWaiter={perNs sendNs}|sendRegPerWaiter={regNs sendNs}|recvNs={recvNs}|recvPerWaiter={perNs recvNs}|recvRegPerWaiter={regNs recvNs}|ctlNs={ctlNs}|ctlPerWaiter={perNs ctlNs}|natAppendNs={appNs}|natConsNs={consNs}|natSum={chk}|load={load}"

/-- The machine's 1-minute load average, so a reading carries the load it was taken under (§1). -/
def chanLoadAvg : IO String := do
  try
    let s ← IO.FS.readFile "/proc/loadavg"
    return (s.splitOn " ").headD "?"
  catch _ => return "?"

/-- **One served channel operation, decomposed.** The `syncbench|` channel row prices the whole served
send/receive at a capacity-`n` channel — where, as its own comment records, the queue reaches its bound only
as the last send completes and the send-park path is therefore never taken — and attributes the residual
against `Std.Channel` to "the per-operation step machinery" without pricing any of it. This mode prices the
parts, in one invocation and beside the stock channel measured in that same run, so the parts have the whole
they decompose.

Every figure is nanoseconds per operation over `n = 2000`, printed and never asserted (§1: a timing assertion
is a flake with a schedule):

* `nsWhole` — the `syncbench|` construction itself: `n` sends into a capacity-`n` channel then `n` receives,
  driven through `Runtime.run`. This is the number the row prints, so the parts have something to sum to.
* `nsStd` — the same `n` messages through the stock channel in this same run, so the pair stays intact.
* `nsLoopAsync` — the same program shape with `pure ()` in place of every send and receive: the CPS closure
  chain and the `forIn`/`bind` skeleton of the `Async` path, with no channel in it, per message.
* `nsLoopIo` — the `IO` loop skeleton alone, per message, the baseline the two transaction rows are read
  against.
* `nsServedTx` — the served transaction through the public `trySend`/`tryRecv`, which run the *same* critical
  section a served `send`/`recv` step runs (prune, the room check, enqueue/dequeue, the wake and the store),
  with `nsLoopIo` subtracted; the figure to compare against `--runtime-unit`'s bare-plumbing rows.
* `nsBareTx` — a bare `Std.Mutex.atomically` (read the state, write it back) over the *same* `ChanState`, with
  `nsLoopIo` subtracted; the delta to `nsServedTx` is what prune and the enqueue/dequeue and the wake add.
* `nsPruneWalk` / `nsEnqueue` — that delta split in two, per message (`nsOpPrune`/`nsOpEnqueue`, per
  operation, and the raw per-operation `nsOpBare`/`nsOpServed` beside them). A full capacity-1 channel's
  `trySend` runs the served branch's `else` — the `live`/`prune` walk over the two waiter lists, the room
  check and the state write, enqueuing nothing; a roomy channel's `trySend`/`tryRecv` run the `then` and add
  the enqueue or the dequeue and the wake. The walk and the enqueue sum to `nsPruneEnqueue`.
* `nsJoinPark` — `Join.new` then `Join.onReady`, the cell a **parked** waiter registers and parks on. The
  served path never reaches it (the capacity-`n` channel never fills), so its contribution to `nsWhole` is
  zero; the row prices the park path the served row does not take.
* `nsStep` — `Item.ofAction` plus `Item.stamp`, one step as a `Task.Async` operation costs it. The served run
  constructs one root `Item.ofIndexed` for the whole `2n`-operation program, so its contribution to `nsWhole`
  is zero; the row prices one step.
* `nsCtx` — the `Ctx` record's two `BaseIO` closure fields, the `BaseIO` boundary a step carries.
* `nsNative` — a native `Task` spawn+join, this window's calibration (§1).

The channel's waiter lists are empty throughout the served path, so `live`'s `liftM`/`filterM` runs over `[]`
and cannot be priced apart from prune without a non-empty list — which needs the park path. That is stated
rather than approximated. -/
def chanDecomp : IO String := do
  let n := 2000
  let k := 20000
  -- Best of two, divided by the operation count, so it is nanoseconds per operation, like `--runtime-unit`.
  let bestNs (iters : Nat) (x : IO Unit) : IO Nat := do
    let mut b := 0
    for _ in List.range 2 do
      let t0 ← IO.monoNanosNow
      x
      let t1 ← IO.monoNanosNow
      if b == 0 || t1 - t0 < b then b := t1 - t0
    return b / iters
  -- The whole served operation: the `syncbench|` construction, per message.
  let nsWhole ← bestNs n do
    let c ← LeanIn.Task.Sync.Channel.new Nat n
    let e ← Sched.Executor.new LeanIn.Task.Item 256 1
    let _ ← Runtime.run e (do
      for i in List.range n do LeanIn.Task.Sync.Channel.send c i
      for _ in List.range n do
        let _ ← LeanIn.Task.Sync.Channel.recv c
        pure ())
    pure ()
  -- The stock channel, same run and same message count.
  let nsStd ← bestNs n do
    let c ← Std.Channel.new (some n)
    for i in List.range n do
      let _ ← IO.wait (← Std.Channel.send c i)
      let _ ← IO.wait (← Std.Channel.recv c)
  -- The `Async` loop skeleton with no channel: the CPS closure chain and the `forIn`/`bind`, per message.
  let nsLoopAsync ← bestNs n do
    let e ← Sched.Executor.new LeanIn.Task.Item 256 1
    let _ ← Runtime.run e (do
      for _ in List.range n do (pure () : LeanIn.Task.Async Unit)
      for _ in List.range n do (pure () : LeanIn.Task.Async Unit))
    pure ()
  -- The `IO` loop skeleton alone, per message.
  let nsLoopIo ← bestNs n do
    for _ in List.range (2 * n) do pure ()
  -- The served transaction split, **per operation**. A full capacity-1 channel's `trySend` runs the served
  -- branch's `else`: `prune` the two waiter lists, check the room, write the state back, enqueue nothing. A
  -- roomy channel's `trySend`/`tryRecv` run the `then`: the same prune and check, then the enqueue or the
  -- dequeue and the wake. The per-message `nsServedTx`/`nsBareTx` and the halves `nsPruneWalk`/`nsEnqueue`
  -- are all derived from these three, so the halves sum to `nsPruneEnqueue` by construction rather than to
  -- within two independent best-of-two samples' noise.
  let nsOpBare ← bestNs (2 * n) do
    let c ← LeanIn.Task.Sync.Channel.new Nat 1
    for _ in List.range (2 * n) do
      c.state.atomically do let st ← get; set st
  let nsOpFull ← bestNs (2 * n) do
    let c ← LeanIn.Task.Sync.Channel.new Nat 1
    let _ ← LeanIn.Task.Sync.Channel.trySend c 0 noWaiterPush
    for i in List.range (2 * n) do
      let _ ← LeanIn.Task.Sync.Channel.trySend c i noWaiterPush
  let nsOpServed ← bestNs (2 * n) do
    let c ← LeanIn.Task.Sync.Channel.new Nat n
    for i in List.range n do
      let _ ← LeanIn.Task.Sync.Channel.trySend c i noWaiterPush
    for _ in List.range n do
      let _ ← LeanIn.Task.Sync.Channel.tryRecv c noWaiterPush
  -- The parked waiter's cell, per registration. `onReady` carries the registering step's context, which is
  -- never used here — the cell is never resolved, so nothing is ever delivered.
  let benchCtx : LeanIn.Task.Ctx :=
    { cancel := ← LeanIn.Task.Cancel.new
    , resume := noWaiterPush
    , routeAt := fun _ => noWaiterPush
    , resumeShared := noWaiterPush
    , «local» := {} }
  let nsJoinPark ← bestNs k do
    for _ in List.range k do
      let j ← LeanIn.Task.Join.new (α := Unit)
      LeanIn.Task.Join.onReady j benchCtx (fun _ _ => pure ())
  -- One step, per step.
  let cancel ← LeanIn.Task.Cancel.new
  let nsStep ← bestNs k do
    for _ in List.range k do
      let it := LeanIn.Task.Item.stamp (LeanIn.Task.Item.ofAction (pure ())) cancel
      if it.cancel.isNone then IO.println "chanunit: the stamp left the token empty"
  -- The `Ctx` record's three `BaseIO` closure fields, per construction.
  let nsCtx ← bestNs k do
    for _ in List.range k do
      let ctx : LeanIn.Task.Ctx :=
        { cancel := cancel
        , resume := fun (_ : LeanIn.Task.Item) => (pure () : BaseIO Unit)
        , routeAt := fun (_ : Nat) (_ : LeanIn.Task.Item) => (pure () : BaseIO Unit)
        , resumeShared := fun (_ : LeanIn.Task.Item) => (pure () : BaseIO Unit)
        , «local» := {} }
      if ctx.cancel.id == 0 then IO.println "chanunit: the ctx has no token"
  -- This window's native calibration: a native `Task` spawned and joined.
  let nsNative ← bestNs k do
    for _ in List.range k do
      let t ← IO.asTask (pure ()) _root_.Task.Priority.default
      let _ ← IO.wait t
  let nsServedTx := 2 * nsOpServed - nsLoopIo
  let nsBareTx := 2 * nsOpBare - nsLoopIo
  let nsOpPrune := nsOpFull - nsOpBare
  let nsOpEnqueue := nsOpServed - nsOpFull
  let nsPruneWalk := 2 * nsOpPrune
  let nsEnqueue := 2 * nsOpEnqueue
  let ours := max 1 nsWhole
  return s!"n={n}|nsWhole={ours}|nsStd={nsStd}|chanRatioPct={nsStd * 100 / ours}|nsServedTx={nsServedTx}|nsBareTx={nsBareTx}|nsPruneEnqueue={nsServedTx - nsBareTx}|nsPruneWalk={nsPruneWalk}|nsEnqueue={nsEnqueue}|nsOpBare={nsOpBare}|nsOpPrune={nsOpPrune}|nsOpEnqueue={nsOpEnqueue}|nsOpServed={nsOpServed}|nsLoopAsync={nsLoopAsync}|nsLoopIo={nsLoopIo}|nsChanWork={nsWhole - nsLoopAsync}|nsJoinPark={nsJoinPark}|nsStep={nsStep}|nsCtx={nsCtx}|nsNative={nsNative}|load={← chanLoadAvg}"

/-- Print the served channel operation's decomposition alone: the whole served send/receive, its parts, and
the stock channel beside it, all in one run. Diagnostic, printed and never asserted — `lake exe controls
--runtime-chan`, and the same `chanunit|` line is printed from `--runtime-sync` beside `syncbench|`. -/
def runtimeChan : IO UInt32 := do
  IO.println s!"chanunit|{← chanDecomp}"
  return 0

/-- **SC13's mode.** One invocation, one `Runtime.run`: the mutex clause, the channel flood with its
control, the semaphore's count, and the three cancellation laws, each probe non-parking so a locked-out
or lost-value production state prints a field rather than hanging. -/
def runtimeSync : IO UInt32 := do
  let hooks ← Runtime.Hooks.new
  let e ← Sched.Executor.new LeanIn.Task.Item 256 1
  let order ← IO.mkRef ([] : List String)
  let aResultRef ← IO.mkRef (0 : Nat)
  let bResultRef ← IO.mkRef (0 : Nat)
  let tryAccRef ← IO.mkRef (0 : Nat)
  let tryRejRef ← IO.mkRef (0 : Nat)
  let parkedRef ← IO.mkRef (0 : Nat)
  let ctlAccRef ← IO.mkRef (0 : Nat)
  let ctlRejRef ← IO.mkRef (0 : Nat)
  let semAccRef ← IO.mkRef (0 : Nat)
  let semRejRef ← IO.mkRef "no"
  let semAfterRef ← IO.mkRef "no"
  let lockRef ← IO.mkRef "no"
  let recvRef ← IO.mkRef "none"
  let ghostRef ← IO.mkRef "none"
  let sendAccRef ← IO.mkRef "no"
  let record (s : String) : IO Unit := order.modify (fun l => l ++ [s])
  let setNat (r : IO.Ref Nat) (v : Nat) : IO Unit := do r.set v
  let addNat (r : IO.Ref Nat) (v : Nat) : IO Unit := do r.modify (fun x => x + v)
  let setStr (r : IO.Ref String) (v : String) : IO Unit := do r.set v
  let gateResolve (p : IO.Promise (Except IO.Error Unit)) : IO Unit := do p.resolve (Except.ok ())

  let cap := 2
  let sent := cap + 1

  let m ← LeanIn.Task.Sync.Mutex.new
  let aGate ← (IO.Promise.new : IO (IO.Promise (Except IO.Error Unit)))
  let bGate ← (IO.Promise.new : IO (IO.Promise (Except IO.Error Unit)))
  let bReady ← (IO.Promise.new : IO (IO.Promise (Except IO.Error Unit)))

  let unrelatedFirst : LeanIn.Task.Async Unit := do
    let _ ← Runtime.awaitPromiseE hooks bReady
    record "u"
    gateResolve aGate
  let unrelatedSecond : LeanIn.Task.Async Unit := do
    record "u"
    gateResolve bGate
  let holderB : LeanIn.Task.Async Nat := do
    gateResolve bReady
    LeanIn.Task.Sync.Mutex.lock m
    record "b-enter"
    let _ ← LeanIn.Task.Async.spawn unrelatedSecond
    let _ ← Runtime.awaitPromiseE hooks bGate
    record "b-exit"
    let push ← LeanIn.Task.Async.push
    LeanIn.Task.Sync.Mutex.unlock m push
    return 9
  let holderA : LeanIn.Task.Async Nat := do
    LeanIn.Task.Sync.Mutex.lock m
    record "a-enter"
    let hb ← LeanIn.Task.Async.spawn holderB
    let _ ← LeanIn.Task.Async.spawn unrelatedFirst
    let _ ← Runtime.awaitPromiseE hooks aGate
    record "a-exit"
    let push ← LeanIn.Task.Async.push
    LeanIn.Task.Sync.Mutex.unlock m push
    let vb ← LeanIn.Task.Async.await hb
    setNat bResultRef vb
    return 7

  let program : LeanIn.Task.Async Unit := do
    let ha ← LeanIn.Task.Async.spawn holderA
    let va ← LeanIn.Task.Async.await ha
    setNat aResultRef va

    -- the flood: `sent` non-parking sends against a channel of `cap`, then the same count again with
    -- `recv` draining as they park; the control channel is the same count into a channel with room.
    let c ← LeanIn.Task.Sync.Channel.new Nat cap
    for i in List.range sent do
      let push ← LeanIn.Task.Async.push
      let ok ← LeanIn.Task.Sync.Channel.trySend c (100 + i) push
      addNat (if ok then tryAccRef else tryRejRef) 1
    let senders ← (List.range sent).mapM (fun i => LeanIn.Task.Async.spawn (do
      LeanIn.Task.Sync.Channel.send c (200 + i)
      addNat parkedRef 1))
    for _ in List.range sent do
      let _ ← LeanIn.Task.Sync.Channel.recv c
      pure ()
    for h in senders do
      let _ ← LeanIn.Task.Async.await h
      pure ()

    let ctl ← LeanIn.Task.Sync.Channel.new Nat sent
    for i in List.range sent do
      let push ← LeanIn.Task.Async.push
      let ok ← LeanIn.Task.Sync.Channel.trySend ctl (300 + i) push
      addNat (if ok then ctlAccRef else ctlRejRef) 1

    -- the semaphore's count: two permits, a third refused, one release, one more admitted.
    let sem ← LeanIn.Task.Sync.Semaphore.new 2
    let s1 ← LeanIn.Task.Sync.Semaphore.tryAcquire sem
    let s2 ← LeanIn.Task.Sync.Semaphore.tryAcquire sem
    let s3 ← LeanIn.Task.Sync.Semaphore.tryAcquire sem
    setNat semAccRef ((if s1 then 1 else 0) + (if s2 then 1 else 0))
    setStr semRejRef (if s3 then "yes" else "no")
    let semPush ← LeanIn.Task.Async.push
    LeanIn.Task.Sync.Semaphore.release sem semPush
    let s4 ← LeanIn.Task.Sync.Semaphore.tryAcquire sem
    setStr semAfterRef (if s4 then "yes" else "no")

    -- (a) a cancelled lock waiter is not granted the lock: this computation holds the mutex, the
    -- waiter parks on it, the waiter is cancelled, the mutex is released, and a non-parking tryLock
    -- reads whether the permit is still there.
    let m2 ← LeanIn.Task.Sync.Mutex.new
    let wReady ← (IO.Promise.new : IO (IO.Promise (Except IO.Error Unit)))
    LeanIn.Task.Sync.Mutex.lock m2
    let w ← LeanIn.Task.Async.spawn (do
      gateResolve wReady
      LeanIn.Task.Sync.Mutex.lock m2)
    let _ ← Runtime.awaitPromiseE hooks wReady
    let wPush ← LeanIn.Task.Async.push
    Runtime.cancel hooks w wPush ()
    LeanIn.Task.Sync.Mutex.unlock m2 wPush
    let got ← LeanIn.Task.Sync.Mutex.tryLock m2
    setStr lockRef (if got then "yes" else "no")

    -- (b) a cancelled receiver consumes no message: the receiver parks on an empty channel, is
    -- cancelled, one value is sent, and a non-parking tryRecv reads whether it is still there.
    let rc ← LeanIn.Task.Sync.Channel.new Nat 1
    let rReady ← (IO.Promise.new : IO (IO.Promise (Except IO.Error Unit)))
    let r ← LeanIn.Task.Async.spawn (do
      gateResolve rReady
      let _ ← LeanIn.Task.Sync.Channel.recv rc
      pure ())
    let _ ← Runtime.awaitPromiseE hooks rReady
    let rPush ← LeanIn.Task.Async.push
    Runtime.cancel hooks r rPush ()
    LeanIn.Task.Sync.Channel.send rc 42
    -- The receiver's value is taken by its own stock task once the send resolves its queue entry; that
    -- task runs on the pool, so the probe waits for a stock completion scheduled after the send before
    -- reading the channel. The wait is a completion, not a clock.
    let settle ← IO.asTask (pure (Except.ok () : Except IO.Error Unit)) _root_.Task.Priority.default
    let _ ← Runtime.awaitTask hooks settle
    let gotRPush ← LeanIn.Task.Async.push
    let gotR ← LeanIn.Task.Sync.Channel.tryRecv rc gotRPush
    setStr recvRef (match gotR with | some _ => "present" | none => "lost")

    -- (c) a cancelled sender consumes no slot: the sender parks on a full channel, is cancelled,
    -- one value is drained, and a non-parking trySend reads whether a slot is free and whether the
    -- cancelled sender's value has appeared.
    let sc ← LeanIn.Task.Sync.Channel.new Nat 1
    let scPush ← LeanIn.Task.Async.push
    let _ ← LeanIn.Task.Sync.Channel.trySend sc 901 scPush
    let sReady ← (IO.Promise.new : IO (IO.Promise (Except IO.Error Unit)))
    let s ← LeanIn.Task.Async.spawn (do
      gateResolve sReady
      LeanIn.Task.Sync.Channel.send sc 999)
    let _ ← Runtime.awaitPromiseE hooks sReady
    let sPush ← LeanIn.Task.Async.push
    Runtime.cancel hooks s sPush ()
    let _ ← LeanIn.Task.Sync.Channel.tryRecv sc sPush
    let sentOk ← LeanIn.Task.Sync.Channel.trySend sc 555 sPush
    let held ← LeanIn.Task.Sync.Channel.tryRecv sc sPush
    setStr sendAccRef (if sentOk then "yes" else "no")
    setStr ghostRef (match held with
      | some v => if v == 999 then "present" else "absent"
      | none   => "absent")
    pure ()

  let runAt ← IO.monoNanosNow
  let _ ← Runtime.run e program
  let returnedAt ← IO.monoNanosNow
  let ord ← order.get
  IO.println s!"sync|cap={cap}|order={String.intercalate "," ord}|aResult={← aResultRef.get}|bResult={← bResultRef.get}|sent={sent}|tryAccepted={← tryAccRef.get}|tryRejected={← tryRejRef.get}|parkedDelivered={← parkedRef.get}|controlAccepted={← ctlAccRef.get}|controlRejected={← ctlRejRef.get}|semAccepted={← semAccRef.get}|semRejected={← semRejRef.get}|semAfterRelease={← semAfterRef.get}|cancelLockAcquired={← lockRef.get}|cancelRecvValue={← recvRef.get}|cancelSendGhost={← ghostRef.get}|cancelSendAccepted={← sendAccRef.get}|runUs={(returnedAt - runAt) / 1000}"
  IO.println syncCtlLine
  let bench ← syncBench
  IO.println s!"syncbench|{bench}"
  waiterBench
  IO.println s!"chanunit|{← chanDecomp}"
  return 0

/-- The service run's own annotations, appended under one `Std.Mutex`: the ordered `events` list of
`(isBegin, id)` the mode reduces to `liveHighWater`, the outcome lists each body appends where it
happened, and the online readings `live`/`parked` with their running maxima. The bodies and the
client's read of the admission log take the same lock, so a begin the client sees is a begin the
record holds. -/
private structure ServiceLog where
  events : List (Bool × Nat) := []
  completed : List Nat := []
  closed : List Nat := []
  responded : List Nat := []
  errored : List Nat := []
  live : Nat := 0
  parked : Nat := 0
  parkedHigh : Nat := 0
  deadlineFired : Bool := false

/-- The `service|` record's fields, in the order the mode prints them. -/
def serviceFields : List String :=
  ["bound", "offered", "accepted", "completed", "closed", "liveHighWater", "parkedAtPeak",
   "requests", "responded", "errored", "deadlineFired", "carrier", "runUs"]

/-- One field of a `key=value|…` record: its value when the key appears exactly once and nonempty,
and `none` when it is absent, repeated or empty — so a value is never bound from a neighbour. -/
def serviceField (rec key : String) : Option String :=
  let vals := (rec.splitOn "|").filterMap (fun tok =>
    match tok.splitOn "=" with
    | [k, v] => if k == key then some v else none
    | _      => none)
  match vals with
  | [v] => if v == "" then none else some v
  | _   => none

/-- A nonempty natural field. -/
def serviceNat (rec key : String) : Option Nat :=
  (serviceField rec key).bind String.toNat?

/-- The record's fields are exactly `serviceFields`, in order, each nonempty. -/
def serviceShaped (rec : String) : Bool :=
  let toks := rec.splitOn "|"
  toks.length == serviceFields.length &&
  (toks.zip serviceFields).all (fun (tok, key) =>
    match tok.splitOn "=" with
    | [k, v] => k == key && v != ""
    | _      => false)

/-- A bracketed `[i,…]` identity list as a multiset of naturals. An empty body, an empty entry or a
non-natural entry yields `none`, so a dropped, doubled or malformed entry is rejected before any
membership is compared. -/
def serviceIds (rec key : String) : Option (List Nat) :=
  (serviceField rec key).bind fun v =>
    if v.startsWith "[" && v.endsWith "]" then
      let body := ((v.drop 1).dropEnd 1).toString
      (body.splitOn ",").mapM (fun s => String.toNat? s)
    else none

/-- Two identity lists hold the same ids with the same multiplicities. -/
def serviceMultisetEq (a b : List Nat) : Bool :=
  a.length == b.length &&
  a.all (fun x => (a.filter (fun y => y == x)).length == (b.filter (fun y => y == x)).length)

/-- Obligation 1 (`Service.NoDrop`): `completed ∪ closed` is exactly `accepted`, and both paths are
populated — so the equality is not carried by one path alone. -/
def serviceNoDropOk (rec : String) : Bool :=
  match serviceIds rec "accepted", serviceIds rec "completed", serviceIds rec "closed" with
  | some acc, some comp, some clo =>
      !comp.isEmpty && !clo.isEmpty && serviceMultisetEq (comp ++ clo) acc
  | _, _, _ => false

/-- Obligation 2 (`Service.Bounded`): the live high-water is within the bound and reaches it, and the
mode's second reading of the same count reaches it too. -/
def serviceBoundedOk (rec : String) : Bool :=
  match serviceNat rec "bound", serviceNat rec "liveHighWater", serviceNat rec "parkedAtPeak" with
  | some b, some lhw, some pap => 1 <= b && lhw <= b && lhw == b && pap == b
  | _, _, _ => false

/-- Obligation 3 (`Service.RequestsResolved` and `Service.PendingWithinLive`): `responded ∪ errored`
is exactly `requests`, disjointly, and the deadline fired — with both outcome paths populated. -/
def serviceResolvedOk (rec : String) : Bool :=
  match serviceIds rec "requests", serviceIds rec "responded", serviceIds rec "errored" with
  | some req, some resp, some err =>
      serviceField rec "deadlineFired" == some "yes" &&
      !resp.isEmpty && !err.isEmpty &&
      serviceMultisetEq (resp ++ err) req &&
      resp.all (fun x => !(err.contains x))
  | _, _, _ => false

/-- The record satisfies every binding of the contract: it is shaped as `serviceFields`, and each of
the three obligations holds, read from its own named fields. -/
def serviceOk (rec : String) : Bool :=
  serviceShaped rec && serviceNoDropOk rec && serviceBoundedOk rec && serviceResolvedOk rec

/-- The checker's verdict as one word, so a reading is `accepted` or `rejected` and nothing else. -/
def serviceReading (b : Bool) : String := if b then "accepted" else "rejected"

/-- A well-formed `service|` record, built from the record syntax and the expected values rather than
from the mode's output, so the checker's controls cannot agree with the mode by construction. -/
def serviceGoodRec : String :=
  "bound=2|offered=[0,1,2,3,4]|accepted=[0,1,2,3,4]|completed=[0,2,4]|closed=[1,3]|liveHighWater=2|parkedAtPeak=2|requests=[0,1,2,3,4]|responded=[0,2,4]|errored=[1,3]|deadlineFired=yes|carrier=100|runUs=1"

/-- A connection silently dropped (O1). -/
def serviceNearMissing : String := serviceGoodRec.replace "completed=[0,2,4]" "completed=[0,2]"

/-- A connection terminated twice (O1). -/
def serviceNearDoubled : String := serviceGoodRec.replace "closed=[1,3]" "closed=[0,1,3]"

/-- The bound not held (O2). -/
def serviceNearOverBound : String := serviceGoodRec.replace "liveHighWater=2" "liveHighWater=3"

/-- A reader that never saw the populated state (O2's negative control). -/
def serviceNearZeroPeak : String := serviceGoodRec.replace "liveHighWater=2" "liveHighWater=0"

/-- A request left silently unresolved (O3). -/
def serviceNearUnresolved : String := serviceGoodRec.replace "requests=[0,1,2,3,4]" "requests=[0,1,2,3,4,5]"

/-- An O3 reader that never exercised the deadline path. -/
def serviceNearNoDeadline : String :=
  (serviceGoodRec.replace "deadlineFired=yes" "deadlineFired=no").replace "errored=[1,3]" "errored=[]"

/-- The mode's own checker readings, on a well-formed record and on each near miss: `accepted` then
`rejected` when the checker discriminates. -/
def serviceCtlLine : String :=
  "servicectl|recordGood=" ++ serviceReading (serviceOk serviceGoodRec) ++
  "|missingId=" ++ serviceReading (serviceOk serviceNearMissing) ++
  "|doubled=" ++ serviceReading (serviceOk serviceNearDoubled) ++
  "|overBound=" ++ serviceReading (serviceOk serviceNearOverBound) ++
  "|zeroPeak=" ++ serviceReading (serviceOk serviceNearZeroPeak) ++
  "|unresolved=" ++ serviceReading (serviceOk serviceNearUnresolved) ++
  "|noDeadline=" ++ serviceReading (serviceOk serviceNearNoDeadline)

/-- **SC14 — the service's own obligations at the executor boundary.**

An accept loop of ours serves `n` connections on one carrier, and `Std.Async`'s client is the peer.
Each connection's body `recv`s the id the client staged, appends `begin id` to a `Std.Mutex`-guarded
log as its first action, then produces its staged response: id `1`'s response is `Runtime.never`, so
its deadline fires; id `3`'s response fails with a staged error; ids `0`, `2`, `4` echo and stay live
until the client closes them. The client connects every socket and sends the staged ids last, waits
until the log holds the bound's worth of begins, and then reads each admitted socket in the server's
own begin order and closes it — so the read order is the server's, not the scheduler's, and no read
waits on a socket the loop has not admitted.

The one `service|` record binds the three obligations to their own fields: `completed ∪ closed =
accepted` (`Service.NoDrop`), `liveHighWater ≤ bound` with `liveHighWater = bound`
(`Service.Bounded`), and `responded ∪ errored = requests` with `deadlineFired = yes`
(`Service.RequestsResolved` / `Service.PendingWithinLive`). `offered` and `carrier` are recorded;
`runUs` is printed and never asserted. The mode also prints its own checker's verdicts on a
well-formed record and on near misses on a `servicectl|` line.

Diagnostic: `lake exe controls --runtime-service [--bound=2]`. -/
def runtimeService (bound : Nat) : IO UInt32 := do
  let n := 5
  let timeout : Std.Time.Millisecond.Offset := 100
  let sendOrder : List Nat := [0, 2, 4, 1, 3]
  let hooks ← Runtime.Hooks.new
  let clock := Runtime.Clock.live hooks
  let l ← Runtime.Listener.bind (Runtime.loopback 0)
  let keep ← IO.mkRef l
  let addrRef ← IO.mkRef (none : Option Std.Net.SocketAddress)
  let e ← Sched.Executor.new LeanIn.Task.Item 256 1
  let svc ← Std.Mutex.new ({} : ServiceLog)
  let svcRead : IO ServiceLog := svc.atomically get
  let svcWrite (f : ServiceLog → ServiceLog) : IO Unit := svc.atomically do set (f (← get))
  let carrier ← IO.getTID
  let startAt ← IO.mkRef (0 : Nat)
  let body : Runtime.Conn → LeanIn.Task.EAsync IO.Error Unit := fun c => do
    -- The connection's own failure is its outcome, recorded before it is raised: the loop awaits every
    -- spawned body, so a body that raised would fail the run rather than close one connection. Catch it
    -- here, at the connection boundary, so the run returns and the record carries `closed`/`errored`.
    try
      match ← Runtime.Conn.recv c hooks 1 with
      | none => pure ()
      | some bs =>
        let id := (bs.get! 0).toNat
        monadLift (svcWrite fun s =>
          { s with events := s.events ++ [(true, id)], live := s.live + 1,
                   parked := s.parked + 1, parkedHigh := max s.parkedHigh (s.parked + 1) })
        let endConn (ok : Bool) : LeanIn.Task.EAsync IO.Error Unit := do
          monadLift (svcWrite fun s =>
            { s with events := s.events ++ [(false, id)], live := s.live - 1, parked := s.parked - 1 })
          if ok then pure () else throw (.userError "connection did not complete")
        if id == 1 then
          let fired ← LeanIn.Task.EAsync.ofAsync (Runtime.withTimeout clock timeout
            (Runtime.never : LeanIn.Task.Async Unit))
          monadLift (svcWrite fun s =>
            { s with errored := s.errored ++ [id], closed := s.closed ++ [id],
                     deadlineFired := fired.isNone })
          endConn false
        else if id == 3 then
          monadLift (svcWrite fun s =>
            { s with errored := s.errored ++ [id], closed := s.closed ++ [id] })
          endConn false
        else
          Runtime.Conn.send c hooks bs
          monadLift (svcWrite fun s => { s with responded := s.responded ++ [id] })
          match ← Runtime.Conn.recv c hooks 65536 with
          | none =>
            monadLift (svcWrite fun s => { s with completed := s.completed ++ [id] })
            endConn true
          | some _ => endConn true
    catch _ => pure ()
  let server ← IO.asTask (Runtime.run e (do
    let a ← Runtime.Listener.sockName (← keep.get)
    addrRef.set (some a)
    startAt.set (← IO.monoNanosNow)
    let r ← Runtime.serveBounded hooks (← keep.get) bound n body
    return r)) _root_.Task.Priority.dedicated
  let addr ← do
    let mut a : Option Std.Net.SocketAddress := none
    while a.isNone do a ← addrRef.get
    pure (a.getD (Runtime.loopback 0))
  -- The client's close discipline is the loop's admission policy: the loop admits `bound` and then
  -- waits on a permit, so a close is what releases one. The client reads and closes in the server's
  -- begin order as each begin arrives, and it reads nothing until it has seen `bound` begins — which is
  -- what makes the live high-water `bound` structural rather than a race.
  Std.Async.Async.block do
    let entries ← sendOrder.mapM (fun id => do
      let c ← Std.Async.TCP.Socket.Client.mk
      c.connect addr
      c.send (ByteArray.mk #[UInt8.ofNat id])
      return (id, c))
    let beginsNow : Std.Async.Async (List Nat) := do
      let s ← svcRead
      return (s.events.filter (fun ev => ev.1)).map (fun ev => ev.2)
    let waitFor (k : Nat) : Std.Async.Async Unit := do
      let mut seen ← beginsNow
      while seen.length < k do
        Std.Async.sleep 1
        seen ← beginsNow
      pure ()
    waitFor bound
    for k in List.range n do
      waitFor (k + 1)
      let ids ← beginsNow
      let id := ids.getD k 0
      match entries.find? (fun (i, _) => i == id) with
      | some (_, c) =>
        let _ ← c.recv? 65536
        c.shutdown
      | none => pure ()
  let outcome ← IO.wait server
  let returnedAt ← IO.monoNanosNow
  match outcome with
  | .error err => IO.println s!"service|failed={err}"; return 1
  | .ok (.error err) => IO.println s!"service|failed={err}"; return 1
  | .ok (.ok ()) =>
    let s ← svc.atomically get
    let begins := (s.events.filter (fun ev => ev.1)).map (fun ev => ev.2)
    -- `accepted`/`requests` are multisets: the order bodies began in belongs to the scheduler, so they
    -- are read out in ascending id order, which is the same ids whichever order the loop admitted them.
    let acc := (List.range n).filter (fun i => begins.contains i)
    let mut live := 0
    let mut high := 0
    for ev in s.events do
      live := if ev.1 then live + 1 else live - 1
      high := max high live
    let br (xs : List Nat) : String := "[" ++ String.intercalate "," (xs.map toString) ++ "]"
    let df := if s.deadlineFired then "yes" else "no"
    let runUs := (returnedAt - (← startAt.get)) / 1000
    IO.println s!"service|bound={bound}|offered={br (List.range n)}|accepted={br acc}|completed={br s.completed}|closed={br s.closed}|liveHighWater={high}|parkedAtPeak={s.parkedHigh}|requests={br acc}|responded={br s.responded}|errored={br s.errored}|deadlineFired={df}|carrier={carrier}|runUs={runUs}"
    IO.println serviceCtlLine
    -- The service run's own measurement, printed and never asserted: the whole run's wall time in
    -- microseconds, its per-connection share, and the connections per second that share implies.
    let connsPerSec := if runUs == 0 then 0 else n * 1000000 / runUs
    IO.println s!"servicebench|n={n}|bound={bound}|runUs={runUs}|usPerConn={runUs / n}|connsPerSec={connsPerSec}"
    return 0

/-- The `context|` record's fields, in the order the mode prints them. -/
def registryCtxFields : List String :=
  ["root", "scope", "child", "unrelated", "childAfterPark", "carrierCount", "carrier",
   "childTid", "childOnCarrier", "trace", "runUs"]

/-- The `registry|` record's fields, in the order the mode prints them. -/
def registryRegFields : List String :=
  ["k", "heldBefore", "begins", "liveHighWater", "cancelled", "completions",
   "completedAtDrainReturn", "liveAtDrainReturn", "heldAfter", "drainReturned",
   "cancelOutcome", "cancelledEndByHandler", "carrier", "runUs"]

/-- The record's fields are exactly `fields`, in order, each nonempty. -/
def registryShaped (rec : String) (fields : List String) : Bool :=
  let toks := rec.splitOn "|"
  toks.length == fields.length &&
  (toks.zip fields).all (fun (tok, key) =>
    match tok.splitOn "=" with
    | [k, v] => k == key && v != ""
    | _      => false)

/-- SC15-O1 as a detector: the spawned child read the value its client task installed, the unrelated
computation read the default, the install took effect (`scope ≠ root`), the read happened on the
carrier the root drives, and it happened in the child's resumed step. Every operand is read from its
own named field. -/
def contextOk (rec : String) : Bool :=
  registryShaped rec registryCtxFields &&
  match serviceNat rec "child", serviceNat rec "scope", serviceNat rec "root",
        serviceNat rec "unrelated", serviceField rec "childAfterPark",
        serviceField rec "childOnCarrier", serviceField rec "childTid",
        serviceField rec "carrier" with
  | some child, some scope, some root, some unrelated, some afterPark, some onCarrier,
    some childTid, some carrier =>
      child == scope && unrelated == root && scope != root &&
      afterPark == "yes" && onCarrier == "yes" && childTid == carrier
  | _, _, _, _, _, _, _, _ => false

/-- SC15-O2 as a detector: the registry held `k` handles and all began, every held handler is
accounted for, the drain returned only after the completing handlers finished, the live count fell to
zero and nothing was left held — with the affirmative control that the live high-water reached the
held count. -/
def registryO2Ok (rec : String) : Bool :=
  match serviceNat rec "k", serviceNat rec "heldBefore", serviceNat rec "begins",
        serviceNat rec "liveHighWater", serviceNat rec "cancelled", serviceNat rec "completions",
        serviceNat rec "completedAtDrainReturn", serviceNat rec "liveAtDrainReturn",
        serviceNat rec "heldAfter" with
  | some k, some heldBefore, some begins, some high, some cancelled, some completions,
    some atDrainReturn, some liveAtDrainReturn, some heldAfter =>
      heldBefore == k && begins == k && completions + cancelled == heldBefore &&
      atDrainReturn == completions && liveAtDrainReturn == 0 && heldAfter == 0 &&
      high == heldBefore && heldBefore != 0
  | _, _, _, _, _, _, _, _, _ => false

/-- SC15-O3 as a detector: a caller still awaiting a handle the drain took gets the cancellation, no
step of the cancelled handler ran afterwards, the cancelled handle was not left behind, and the drain
terminated. -/
def registryO3Ok (rec : String) : Bool :=
  serviceField rec "drainReturned" == some "yes" &&
  serviceField rec "cancelOutcome" == some "error" &&
  serviceField rec "cancelledEndByHandler" == some "no" &&
  serviceNat rec "heldAfter" == some 0

/-- The record satisfies every binding of the registry clause: it is shaped as `registryRegFields`,
and both obligations hold, read from their own named fields. -/
def registryOk (rec : String) : Bool :=
  registryShaped rec registryRegFields && registryO2Ok rec && registryO3Ok rec

/-- A well-formed `context|` record, built from the record syntax and the expected values rather than
from the mode's output, so the checker's controls cannot agree with the mode by construction. -/
def contextGoodRec : String :=
  "root=0|scope=7|child=7|unrelated=0|childAfterPark=yes|carrierCount=1|carrier=100|childTid=100|childOnCarrier=yes|trace=sc15|runUs=1"

/-- A well-formed `registry|` record, likewise. -/
def registryGoodRec : String :=
  "k=4|heldBefore=4|begins=4|liveHighWater=4|cancelled=1|completions=3|completedAtDrainReturn=3|liveAtDrainReturn=0|heldAfter=0|drainReturned=yes|cancelOutcome=error|cancelledEndByHandler=no|carrier=100|runUs=1"

/-- No inheritance: the child read the default. -/
def registryCtxNearChildNotInherited : String := contextGoodRec.replace "child=7" "child=0"

/-- The installed value leaked to a computation the client did not spawn. -/
def registryCtxNearSiblingLeak : String := contextGoodRec.replace "unrelated=0" "unrelated=7"

/-- The drain returned before the outstanding handlers finished: the live count is still up and the
snapshot's completion count is short. -/
def registryRegNearDrainEarly : String :=
  (registryGoodRec.replace "completedAtDrainReturn=3" "completedAtDrainReturn=0").replace
    "liveAtDrainReturn=0" "liveAtDrainReturn=3"

/-- Handles left behind by the drain. -/
def registryRegNearHeldLeft : String := registryGoodRec.replace "heldAfter=0" "heldAfter=1"

/-- A step of the cancelled handler ran after its cancellation. -/
def registryRegNearCancelledRanOn : String :=
  registryGoodRec.replace "cancelledEndByHandler=no" "cancelledEndByHandler=yes"

/-- The mode's own checker readings, on a well-formed pair and on each near miss: `accepted` then
`rejected` when the checker discriminates. -/
def registryCtlLine : String :=
  "registryctl|recordGood=" ++ serviceReading (contextOk contextGoodRec && registryOk registryGoodRec) ++
  "|childNotInherited=" ++ serviceReading (contextOk registryCtxNearChildNotInherited && registryOk registryGoodRec) ++
  "|siblingLeak=" ++ serviceReading (contextOk registryCtxNearSiblingLeak && registryOk registryGoodRec) ++
  "|drainEarly=" ++ serviceReading (contextOk contextGoodRec && registryOk registryRegNearDrainEarly) ++
  "|heldLeft=" ++ serviceReading (contextOk contextGoodRec && registryOk registryRegNearHeldLeft) ++
  "|cancelledRanOn=" ++ serviceReading (contextOk contextGoodRec && registryOk registryRegNearCancelledRanOn)

/-- The registry clause's own annotations, appended under one `Std.Mutex`: the ids in begin order, the
ids whose connection lifetime ended (a handler's own end, or the canceller's end for the handle it
cancelled), the online live count and its running maximum, and the number of handlers that reached
their own end. -/
private structure RegistryLog where
  begins : List Nat := []
  ends : List Nat := []
  live : Nat := 0
  liveHigh : Nat := 0
  handled : Nat := 0

/-- **SC15 — the task-local context is inherited, and the registry drains.**

One invocation, on one carrier, reads three things. The context clause installs a `Task.Local` on a
client computation (`Async.withLocal`), spawns a child from it, and has the child read `Async.local`
in a *resumed* step after parking on a gate: the child reads the installed value, a computation
spawned outside the scope reads the default, and no step's signature gains a parameter. The registry
clause registers `k` handlers that begin and park, cancels one, and drains: the drain returns only
after the completing handlers have finished, leaves nothing held, and a caller still holding the
cancelled handle gets the cancellation rather than a hang. The mode also prints this mode's own
checker's verdicts on a well-formed pair and on near misses on a `registryctl|` line, and three
measurement rows, printed and never asserted.

Diagnostic: `lake exe controls --runtime-registry`. -/
def runtimeRegistry : IO UInt32 := do
  let k := 4
  let benchN := 10000
  let e ← Sched.Executor.new LeanIn.Task.Item 256 1
  let hooks ← Runtime.Hooks.new
  let carrier ← IO.getTID
  let startAt ← IO.mkRef (0 : Nat)
  -- MEASUREMENT (printed, never asserted): the add path, the drain path over already-resolved cells,
  -- and the same handles awaited from a bare List by hand.
  let benchReg ← LeanIn.Task.Registry.new (α := Unit)
  let benchE ← Sched.Executor.new LeanIn.Task.Item 256 1
  let benchAddUs ← IO.mkRef (0 : Nat)
  let benchDrainUs ← IO.mkRef (0 : Nat)
  let benchHandUs ← IO.mkRef (0 : Nat)
  let benchProg : LeanIn.Task.EAsync IO.Error Unit := do
    let clock : IO Nat := IO.monoNanosNow
    let t0 ← monadLift clock
    let hs ← (List.range benchN).mapM (fun _ =>
      LeanIn.Task.EAsync.ofAsync (LeanIn.Task.Registry.spawn benchReg (pure () : LeanIn.Task.Async Unit)))
    let t1 ← monadLift clock
    benchAddUs.set (t1 - t0)
    for h in hs do let _ ← LeanIn.Task.EAsync.ofAsync (LeanIn.Task.Async.await h)
    let t2 ← monadLift clock
    LeanIn.Task.EAsync.ofAsync (LeanIn.Task.Registry.drain benchReg)
    let t3 ← monadLift clock
    benchDrainUs.set (t3 - t2)
    let hs2 ← (List.range benchN).mapM (fun _ =>
      LeanIn.Task.EAsync.ofAsync (LeanIn.Task.Async.spawn (pure () : LeanIn.Task.Async Unit)))
    for h in hs2 do let _ ← LeanIn.Task.EAsync.ofAsync (LeanIn.Task.Async.await h)
    let t4 ← monadLift clock
    for h in hs2 do let _ ← LeanIn.Task.EAsync.ofAsync (LeanIn.Task.Async.await h)
    let t5 ← monadLift clock
    benchHandUs.set (t5 - t4)
  let benchOut ← Runtime.run benchE benchProg
  match benchOut with
  | .error err => IO.println s!"registrybench|failed={err}"
  | .ok () => pure ()
  -- The synchronized fake the context clause needs: two IO.Promise gates the mode's own steps
  -- resolve, so the order is enforced by awaits rather than by a clock or a socket.
  let l7 : LeanIn.Task.Local := { requestId := 7, deadline := none, trace := "sc15" }
  let signal ← (IO.Promise.new : IO (IO.Promise (Except IO.Error Unit)))
  let gate ← (IO.Promise.new : IO (IO.Promise (Except IO.Error Unit)))
  let rootRef ← IO.mkRef (0 : Nat)
  let scopeRef ← IO.mkRef (0 : Nat)
  let childRef ← IO.mkRef (0 : Nat)
  let unrelatedRef ← IO.mkRef (0 : Nat)
  let traceRef ← IO.mkRef ""
  let childTidRef ← IO.mkRef (0 : UInt64)
  let childStepRef ← IO.mkRef (0 : Nat)
  -- The registry clause's gates and its one locked log.
  let release ← (IO.Promise.new : IO (IO.Promise (Except IO.Error Unit)))
  let allParked ← (IO.Promise.new : IO (IO.Promise (Except IO.Error Unit)))
  let allEnded ← (IO.Promise.new : IO (IO.Promise (Except IO.Error Unit)))
  let drainStarted ← (IO.Promise.new : IO (IO.Promise (Except IO.Error Unit)))
  let log ← Std.Mutex.new ({} : RegistryLog)
  let logRead : IO RegistryLog := log.atomically get
  let logMod (f : RegistryLog → RegistryLog) : IO Unit := log.atomically do set (f (← get))
  let heldBeforeRef ← IO.mkRef (0 : Nat)
  let heldAfterRef ← IO.mkRef (0 : Nat)
  let snapshotRef ← IO.mkRef (none : Option RegistryLog)
  let drainUsRef ← IO.mkRef (0 : Nat)
  let drainReturnedRef ← IO.mkRef "no"
  let cancelOutcomeRef ← IO.mkRef "none"
  let program : LeanIn.Task.EAsync IO.Error Unit := do
    -- CONTEXT
    let rootLocal ← LeanIn.Task.EAsync.ofAsync LeanIn.Task.Async.local
    rootRef.set rootLocal.requestId
    let bBody : LeanIn.Task.EAsync IO.Error Nat := do
      let l ← LeanIn.Task.EAsync.ofAsync LeanIn.Task.Async.local
      return l.requestId
    -- The child resolves the signal in its first step and parks; it reads `Async.local` only when it
    -- is resumed, so the value is read by a task scheduled on the carrier on its own token.
    let a1Body : LeanIn.Task.EAsync IO.Error (Nat × UInt64) := do
      monadLift (IO.Promise.resolve ((.ok () : Except IO.Error Unit)) signal : BaseIO Unit)
      let _ ← Runtime.awaitPromiseE hooks gate
      childStepRef.set 2
      let l ← LeanIn.Task.EAsync.ofAsync LeanIn.Task.Async.local
      let tid ← monadLift (IO.getTID : IO UInt64)
      return (l.requestId, tid)
    let aBody : LeanIn.Task.EAsync IO.Error (Nat × String × Nat × UInt64) := do
      let l ← LeanIn.Task.EAsync.ofAsync LeanIn.Task.Async.local
      let h ← LeanIn.Task.MonadAsync.spawn a1Body
      let _ ← Runtime.awaitPromiseE hooks signal
      monadLift (IO.Promise.resolve ((.ok () : Except IO.Error Unit)) gate : BaseIO Unit)
      let (child, tid) ← LeanIn.Task.MonadAwait.await h
      return (l.requestId, l.trace, child, tid)
    let bh ← LeanIn.Task.MonadAsync.spawn bBody
    let ah ← LeanIn.Task.MonadAsync.spawn (LeanIn.Task.Async.withLocal l7 aBody)
    let unrelated ← LeanIn.Task.MonadAwait.await bh
    let (scope, trace, child, childTid) ← LeanIn.Task.MonadAwait.await ah
    unrelatedRef.set unrelated
    scopeRef.set scope
    traceRef.set trace
    childRef.set child
    childTidRef.set childTid
    -- REGISTRY
    let handler (id : Nat) : LeanIn.Task.EAsync IO.Error Unit := do
      monadLift (logMod fun s =>
        { s with begins := s.begins ++ [id], live := s.live + 1,
                 liveHigh := max s.liveHigh (s.live + 1) })
      let begun ← monadLift logRead
      if begun.begins.length == k then monadLift (IO.Promise.resolve ((.ok () : Except IO.Error Unit)) allParked : BaseIO Unit)
      let _ ← Runtime.awaitPromiseE hooks release
      monadLift (logMod fun s =>
        { s with ends := s.ends ++ [id], live := s.live - 1, handled := s.handled + 1 })
      let doneN ← monadLift logRead
      if doneN.handled == k - 1 then monadLift (IO.Promise.resolve ((.ok () : Except IO.Error Unit)) allEnded : BaseIO Unit)
    let reg ← monadLift (LeanIn.Task.Registry.new (α := Except IO.Error Unit))
    let hs ← (List.range k).mapM (fun id =>
      LeanIn.Task.EAsync.ofAsync (LeanIn.Task.Registry.spawn reg (handler id)))
    let _ ← Runtime.awaitPromiseE hooks allParked
    let heldBefore ← monadLift (LeanIn.Task.Registry.size reg)
    heldBeforeRef.set heldBefore
    match hs[k - 1]? with
    | none => pure ()
    | some h3 =>
      -- The connection's lifetime ends where the cancellation is issued (SC14's `endConn` shape), so
      -- the cancelling step appends the id to `ends`; the cancelled handler's own append is absent.
      let push ← LeanIn.Task.EAsync.ofAsync LeanIn.Task.Async.push
      monadLift (Runtime.cancel hooks h3 push (.error (.userError "sc15")) : IO Unit)
      monadLift (logMod fun s => { s with ends := s.ends ++ [k - 1], live := s.live - 1 })
      let d : LeanIn.Task.EAsync IO.Error Unit := do
        monadLift (IO.Promise.resolve ((.ok () : Except IO.Error Unit)) drainStarted : BaseIO Unit)
        let t0 ← monadLift (IO.monoNanosNow : IO Nat)
        LeanIn.Task.EAsync.ofAsync (LeanIn.Task.Registry.drain reg)
        let t1 ← monadLift (IO.monoNanosNow : IO Nat)
        drainUsRef.set (t1 - t0)
        let s ← monadLift logRead
        snapshotRef.set (some s)
      let dh ← LeanIn.Task.MonadAsync.spawn d
      let _ ← Runtime.awaitPromiseE hooks drainStarted
      monadLift (IO.Promise.resolve ((.ok () : Except IO.Error Unit)) release : BaseIO Unit)
      let _ ← LeanIn.Task.MonadAwait.await dh
      drainReturnedRef.set "yes"
      let _ ← Runtime.awaitPromiseE hooks allEnded
      let co ← (LeanIn.Task.EAsync.ofAsync (LeanIn.Task.Async.await h3) :
        LeanIn.Task.EAsync IO.Error (Except IO.Error Unit))
      cancelOutcomeRef.set (match co with | .error _ => "error" | .ok _ => "ok")
      let heldAfter ← monadLift (LeanIn.Task.Registry.size reg)
      heldAfterRef.set heldAfter
  startAt.set (← IO.monoNanosNow)
  let outcome ← Runtime.run e program
  match outcome with
  | .error err => IO.println s!"registry|failed={err}"; return 1
  | .ok () =>
    let finalLog ← logRead
    let root0 ← rootRef.get
    let scope ← scopeRef.get
    let child ← childRef.get
    let unrelated ← unrelatedRef.get
    let trace ← traceRef.get
    let childTid ← childTidRef.get
    let childStep ← childStepRef.get
    let heldBefore ← heldBeforeRef.get
    let heldAfter ← heldAfterRef.get
    let snap ← snapshotRef.get
    let drainUs ← drainUsRef.get
    let drainReturned ← drainReturnedRef.get
    let cancelOutcome ← cancelOutcomeRef.get
    let returnedAt ← IO.monoNanosNow
    let runUs := (returnedAt - (← startAt.get)) / 1000
    let childOnCarrier := if childTid == carrier then "yes" else "no"
    let childAfterPark := if childStep == 2 then "yes" else "no"
    let completions := finalLog.handled
    let cancelled := 1
    let liveHighWater := finalLog.liveHigh
    let begins := finalLog.begins.length
    let completedAtDrainReturn := match snap with | some s => s.handled | none => 0
    let liveAtDrainReturn := match snap with | some s => s.live | none => 0
    let threes := (finalLog.ends.filter (fun x => x == k - 1)).length
    let cancelledEndByHandler := if threes >= 2 then "yes" else "no"
    IO.println s!"context|root={root0}|scope={scope}|child={child}|unrelated={unrelated}|childAfterPark={childAfterPark}|carrierCount=1|carrier={carrier}|childTid={childTid}|childOnCarrier={childOnCarrier}|trace={trace}|runUs={runUs}"
    IO.println s!"registry|k={k}|heldBefore={heldBefore}|begins={begins}|liveHighWater={liveHighWater}|cancelled={cancelled}|completions={completions}|completedAtDrainReturn={completedAtDrainReturn}|liveAtDrainReturn={liveAtDrainReturn}|heldAfter={heldAfter}|drainReturned={drainReturned}|cancelOutcome={cancelOutcome}|cancelledEndByHandler={cancelledEndByHandler}|carrier={carrier}|runUs={runUs}"
    IO.println registryCtlLine
    IO.println s!"registrybench|n={benchN}|addUs={(← benchAddUs.get) / 1000}|drainUs={(← benchDrainUs.get) / 1000}|usPerHandle={(← benchDrainUs.get) / benchN}"
    IO.println s!"registryhand|n={benchN}|us={(← benchHandUs.get) / 1000}"
    IO.println s!"registryheld|k={k}|drainUs={drainUs / 1000}"
    return 0

/- **SC16 — selection, racing and priority.**

One invocation of `--runtime-select` reads three clause records. The **selection** clause spawns two
gated computations and a releaser on one carrier, calls `Task.select` in the spawn step before any of
them has run, and records which handle `select` returned, the order the handles became ready, both
values `join` collected, and the loser's own value. The **race** clause spawns a parked loser and a
completing winner and calls `Runtime.race`, reading the loser's outcome and final cell value, the log
of steps that ran, and the registry's outstanding-registration count read immediately after `race`
returned and before the loser's gate is released. The **priority** clause preloads the ring and issues
a `.normal` and a `.high` spawn in both orders, reading the label order the carrier served.

Every compared value is a named field of one of the three records; the mode also prints its own
checker's readings on a well-formed trio and on near misses (`selectctl|`), and four measurement rows,
printed and never asserted.

Diagnostic: `lake exe controls --runtime-select`. -/

/-- The `select|` record's fields, in the order the mode prints them. -/
def selectFields : List String :=
  ["left", "right", "winner", "readyOrder", "winnerValue", "loserValue", "joined", "carrier", "runUs"]

/-- The `race|` record's fields, in the order the mode prints them. -/
def raceFields : List String :=
  ["winner", "loser", "loserOutcome", "loserRanOn", "pendingBefore", "pendingAfter", "winnerRan",
   "loserFinal", "runUs"]

/-- The `priority|` record's fields, in the order the mode prints them. -/
def priorityFields : List String :=
  ["k", "normalThenHigh", "highThenNormal", "servedBeforeHigh", "servedBeforeNormal", "runUs"]

/-- SC16-O1 as a detector: the handle that became ready first is the one `select` returned — `winner`
is the first entry of the run's own readiness log — and the two handles are distinct; the affirmative
control, in the same record, is the concrete expectation `winner=h1` with `readyOrder=h1,h0`, so the
relation is not `x == x`; and `select` left the loser running (`loserValue=10`) and `join` collected
both values in list order (`joined=10,20`). Every operand is read from its own named field. -/
def selectOk (rec : String) : Bool :=
  registryShaped rec selectFields &&
  match serviceField rec "left", serviceField rec "right", serviceField rec "winner",
        serviceField rec "readyOrder", serviceField rec "loserValue",
        serviceField rec "joined" with
  | some left, some right, some winner, some readyOrder, some loserValue, some joined =>
      let parts := readyOrder.splitOn ","
      left != right && parts.length == 2 && parts.head? == some winner &&
      winner == "h1" && readyOrder == "h1,h0" &&
      loserValue == "10" && joined == "10,20"
  | _, _, _, _, _, _ => false

/-- SC16-O2 as a detector: a caller awaiting the cancelled loser gets the race's value (`error`),
no step of the loser ran afterwards, the loser's cell holds the cancellation, and its registration
was retired before the loser's gate was released (`pendingAfter=0`). The affirmative control, in the
same record, is `winnerRan=yes` and `pendingBefore != 0` — the loser was parked with a registration
before the race, so `pendingAfter=0` is a change of state, not a reading of zero. -/
def raceOk (rec : String) : Bool :=
  registryShaped rec raceFields &&
  serviceField rec "loserOutcome" == some "error" &&
  serviceField rec "loserRanOn" == some "no" &&
  serviceField rec "loserFinal" == some "error" &&
  serviceNat rec "pendingAfter" == some 0 &&
  serviceField rec "winnerRan" == some "yes" &&
  (match serviceNat rec "pendingBefore" with | some n => n != 0 | none => false)

/-- SC16-O3 as a detector: a `.high` spawn is served before a `.normal` spawn regardless of issue
order (`normalThenHigh=high,normal` and `highThenNormal=high,normal`), with no preloaded ring item
served before the high task and every one served before the normal task. The control, in the same
record, is `k != 0`, so `servedBeforeNormal == k` is not two zero counts; `highThenNormal` is the
issue-order-reversed repeat that would also pass were the argument ignored. -/
def priorityOk (rec : String) : Bool :=
  registryShaped rec priorityFields &&
  serviceField rec "normalThenHigh" == some "high,normal" &&
  serviceField rec "highThenNormal" == some "high,normal" &&
  serviceNat rec "servedBeforeHigh" == some 0 &&
  (match serviceNat rec "k", serviceNat rec "servedBeforeNormal" with
   | some k, some served => k != 0 && served == k
   | _, _ => false)

/-- A well-formed `select|` record, built from the record syntax and the expectation rather than from
the mode's output, so the checker's controls cannot agree with the mode by construction. -/
def selectGoodRec : String :=
  "left=h0|right=h1|winner=h1|readyOrder=h1,h0|winnerValue=20|loserValue=10|joined=10,20|carrier=100|runUs=1"

/-- The staged red: a later handle became ready first, but the list-ordered `select` returned the head. -/
def selectNearListOrder : String := selectGoodRec.replace "winner=h1" "winner=h0"

/-- A well-formed `race|` record, likewise. -/
def raceGoodRec : String :=
  "winner=w|loser=l|loserOutcome=error|loserRanOn=no|pendingBefore=1|pendingAfter=0|winnerRan=yes|loserFinal=error|runUs=1"

/-- The loser ran on after the race returned. -/
def raceNearRanOn : String := raceGoodRec.replace "loserRanOn=no" "loserRanOn=yes"

/-- The loser's registration was not retired at the race. -/
def raceNearPending : String := raceGoodRec.replace "pendingAfter=0" "pendingAfter=1"

/-- A well-formed `priority|` record, likewise. -/
def priorityGoodRec : String :=
  "k=4|normalThenHigh=high,normal|highThenNormal=high,normal|servedBeforeHigh=0|servedBeforeNormal=4|runUs=1"

/-- The priority argument ignored: the ring served the `.normal` spawn issued first. -/
def priorityNearOrder : String :=
  priorityGoodRec.replace "normalThenHigh=high,normal" "normalThenHigh=normal,high"

/-- The mode's own checker readings: `accepted=yes` when the well-formed select/race/priority trio is
accepted, `rejected=yes` when every near miss is rejected, and `variants=4`, the number of near-miss
variants tested. -/
def selectCtlLine : String :=
  "selectctl|accepted=" ++
    (if selectOk selectGoodRec && raceOk raceGoodRec && priorityOk priorityGoodRec then "yes" else "no") ++
  "|rejected=" ++
    (if !(selectOk selectNearListOrder) && !(raceOk raceNearRanOn) &&
        !(raceOk raceNearPending) && !(priorityOk priorityNearOrder) then "yes" else "no") ++
  "|variants=4"

/-- One priority run: preload `k` parked `.normal` computations (each appending `n<i>` on its first
step, then parking), then a fresh `.normal` task labelled `normal` and a fresh `.high` task labelled
`high` (in `issueHighFirst` order). Each first step appends its label to one `Std.Mutex`-guarded list —
the order the carrier served — and the run returns that list once all `k+2` have run. -/
def priorityRun (k : Nat) (issueHighFirst : Bool) : IO (List String) := do
  let e ← Sched.Executor.new LeanIn.Task.Item 256 1
  let hooks ← Runtime.Hooks.new
  let release ← (IO.Promise.new : IO (IO.Promise (Except IO.Error Unit)))
  let allServed ← (IO.Promise.new : IO (IO.Promise (Except IO.Error Unit)))
  let served ← Std.Mutex.new ([] : List String)
  let count ← IO.mkRef (0 : Nat)
  let servedMod (f : List String → List String) : IO Unit := served.atomically do set (f (← get))
  let record (label : String) : IO Unit := do
    servedMod (fun s => s ++ [label])
    let n ← count.get
    count.set (n + 1)
    if n + 1 == k + 2 then IO.Promise.resolve (.ok ()) allServed
  let parked (label : String) : LeanIn.Task.Async Unit := do
    monadLift (record label)
    let _ ← Runtime.awaitPromiseE hooks release
    pure ()
  let program : LeanIn.Task.EAsync IO.Error Unit := do
    for i in List.range k do
      let _ ← monadLift (Runtime.spawn e Runtime.Priority.normal (parked s!"n{i}"))
      pure ()
    if issueHighFirst then
      let _ ← monadLift (Runtime.spawn e Runtime.Priority.high (parked "high"))
      let _ ← monadLift (Runtime.spawn e Runtime.Priority.normal (parked "normal"))
      pure ()
    else
      let _ ← monadLift (Runtime.spawn e Runtime.Priority.normal (parked "normal"))
      let _ ← monadLift (Runtime.spawn e Runtime.Priority.high (parked "high"))
      pure ()
    let _ ← Runtime.awaitPromiseE hooks allServed
    pure ()
  let _ ← Runtime.run e program
  served.atomically get

/-- The label order in which the two fresh priority tasks were served, read from the served list. -/
def servedLabelOrder (ls : List String) : String :=
  String.intercalate "," (ls.filter (fun l => l == "normal" || l == "high"))

/-- How many preloaded ring labels were served before `target`'s first step. The preloaded labels are
the `n<i>` ones; the two fresh labels are excluded. -/
def servedBefore (target : String) (ls : List String) : Nat :=
  ((ls.takeWhile (fun l => l != target)).filter
    (fun l => l != "normal" && l != "high")).length

/-- One `prioritybench` measurement: preload `k` parked `.normal` tasks, issue one fresh spawn in the
named lane, and time the run to its return. Printed and never asserted; it may read a clock. -/
def priorityOne (k : Nat) (high : Bool) : IO Nat := do
  let e ← Sched.Executor.new LeanIn.Task.Item 256 1
  let hooks ← Runtime.Hooks.new
  let release ← (IO.Promise.new : IO (IO.Promise (Except IO.Error Unit)))
  let allServed ← (IO.Promise.new : IO (IO.Promise (Except IO.Error Unit)))
  let count ← IO.mkRef (0 : Nat)
  let record : IO Unit := do
    let n ← count.get
    count.set (n + 1)
    if n + 1 == k + 1 then IO.Promise.resolve (.ok ()) allServed
  let body : LeanIn.Task.Async Unit := do
    monadLift record
    let _ ← Runtime.awaitPromiseE hooks release
    pure ()
  let program : LeanIn.Task.EAsync IO.Error Unit := do
    for _ in List.range k do
      let _ ← monadLift (Runtime.spawn e Runtime.Priority.normal body)
      pure ()
    let _ ← monadLift (Runtime.spawn e (if high then Runtime.Priority.high else Runtime.Priority.normal) body)
    let _ ← Runtime.awaitPromiseE hooks allServed
    pure ()
  let t0 ← IO.monoNanosNow
  let _ ← Runtime.run e program
  let t1 ← IO.monoNanosNow
  return t1 - t0

/-- `prioritybench`: `n` high and `n` normal spawn-to-first-step timings beside a preloaded ring. -/
def priorityBench (k n : Nat) : IO (Nat × Nat) := do
  let mut highNs := 0
  let mut normalNs := 0
  for _ in List.range n do
    highNs := highNs + (← priorityOne k true)
    normalNs := normalNs + (← priorityOne k false)
  return (highNs, normalNs)

/-- A handle whose cell is already resolved, so a benchmark can await it without a scheduling round. The
cell is *built* resolved (`Join.resolved`) rather than resolved later: nothing can have registered on it, so
there is no waiter to deliver and no route for a resolution to name. -/
def resolvedTask {α : Type} (v : α) : IO (LeanIn.Task.Task α) := do
  let cell ← LeanIn.Task.Join.resolved v
  let token ← LeanIn.Task.Cancel.new
  return ⟨cell, token⟩

/-- **SC16 — selection, racing and priority.**

One invocation on one carrier per clause; the records are `select|`, `race|` and `priority|`, followed
by the checker's `selectctl|` and the measurement rows.

Diagnostic: `lake exe controls --runtime-select`. -/
def runtimeSelect : IO UInt32 := do
  let carrier ← IO.getTID
  -- SELECTION
  let selStart ← IO.monoNanosNow
  let selE ← Sched.Executor.new LeanIn.Task.Item 256 1
  let selHooks ← Runtime.Hooks.new
  let g0 ← (IO.Promise.new : IO (IO.Promise (Except IO.Error Unit)))
  let g1 ← (IO.Promise.new : IO (IO.Promise (Except IO.Error Unit)))
  let readyLog ← Std.Mutex.new ([] : List String)
  let readyMod (f : List String → List String) : IO Unit := readyLog.atomically do set (f (← get))
  let selWinnerRef ← IO.mkRef (0 : Nat)
  let selWinnerValueRef ← IO.mkRef (0 : Nat)
  let selLoserValueRef ← IO.mkRef (0 : Nat)
  let selJoinedRef ← IO.mkRef ([] : List Nat)
  let selProg : LeanIn.Task.EAsync IO.Error Unit := do
    let h0Body : LeanIn.Task.Async Nat := do
      let _ ← Runtime.awaitPromiseE selHooks g0
      monadLift (readyMod (fun s => s ++ ["h0"]))
      return 10
    let h1Body : LeanIn.Task.Async Nat := do
      let _ ← Runtime.awaitPromiseE selHooks g1
      monadLift (readyMod (fun s => s ++ ["h1"]))
      monadLift (IO.Promise.resolve (.ok ()) g0 : BaseIO Unit)
      return 20
    let rBody : LeanIn.Task.Async Unit := do
      monadLift (IO.Promise.resolve (.ok ()) g1 : BaseIO Unit)
    let h0 ← LeanIn.Task.EAsync.ofAsync (LeanIn.Task.Async.spawn h0Body)
    let h1 ← LeanIn.Task.EAsync.ofAsync (LeanIn.Task.Async.spawn h1Body)
    let _hr ← LeanIn.Task.EAsync.ofAsync (LeanIn.Task.Async.spawn rBody)
    let (winner, winnerValue) ← LeanIn.Task.EAsync.ofAsync (LeanIn.Task.select h0 [h1])
    let loser := if winner == 0 then h1 else h0
    let loserValue ← LeanIn.Task.EAsync.ofAsync (LeanIn.Task.Async.await loser)
    let joined ← LeanIn.Task.EAsync.ofAsync (LeanIn.Task.join [h0, h1])
    selWinnerRef.set winner
    selWinnerValueRef.set winnerValue
    selLoserValueRef.set loserValue
    selJoinedRef.set joined
  match ← Runtime.run selE selProg with
  | .error err => IO.println s!"select|failed={err}"; return 1
  | .ok () =>
    let winner ← selWinnerRef.get
    let winnerValue ← selWinnerValueRef.get
    let loserValue ← selLoserValueRef.get
    let joined ← selJoinedRef.get
    let readyOrder ← readyLog.atomically get
    let selUs := (← IO.monoNanosNow) - selStart
    let winnerLabel := if winner == 0 then "h0" else "h1"
    IO.println s!"select|left=h0|right=h1|winner={winnerLabel}|readyOrder={String.intercalate "," readyOrder}|winnerValue={winnerValue}|loserValue={loserValue}|joined={String.intercalate "," (joined.map toString)}|carrier={carrier}|runUs={selUs / 1000}"
  -- RACE
  let raceStart ← IO.monoNanosNow
  let raceE ← Sched.Executor.new LeanIn.Task.Item 256 1
  let raceHooks ← Runtime.Hooks.new
  let gRel ← (IO.Promise.new : IO (IO.Promise (Except IO.Error Unit)))
  let lParked ← (IO.Promise.new : IO (IO.Promise (Except IO.Error Unit)))
  let raceLog ← Std.Mutex.new ([] : List String)
  let raceMod (f : List String → List String) : IO Unit := raceLog.atomically do set (f (← get))
  let rWinnerRef ← IO.mkRef (0 : Nat)
  let rPendingBeforeRef ← IO.mkRef (0 : Nat)
  let rPendingAfterRef ← IO.mkRef (0 : Nat)
  let rLoserOutcomeRef ← IO.mkRef "none"
  let rLoserFinalRef ← IO.mkRef "none"
  let raceProg : LeanIn.Task.EAsync IO.Error Unit := do
    let lBody : LeanIn.Task.Async (Except IO.Error Unit) := do
      monadLift (IO.Promise.resolve (.ok ()) lParked : BaseIO Unit)
      monadLift (raceMod (fun s => s ++ ["l-started"]))
      let _ ← Runtime.awaitPromiseE raceHooks gRel
      monadLift (raceMod (fun s => s ++ ["l-ran"]))
      return .ok ()
    let wBody : LeanIn.Task.Async (Except IO.Error Unit) := do
      monadLift (raceMod (fun s => s ++ ["w-ran"]))
      return .ok ()
    let hl ← LeanIn.Task.EAsync.ofAsync (LeanIn.Task.Async.spawn lBody)
    let hw ← LeanIn.Task.EAsync.ofAsync (LeanIn.Task.Async.spawn wBody)
    let _ ← Runtime.awaitPromiseE raceHooks lParked
    let pendingBefore ← monadLift (Runtime.pending raceHooks)
    let raceV : Except IO.Error Unit := .error (.userError "sc16")
    let (rwinner, _rv) ← LeanIn.Task.EAsync.ofAsync (Runtime.race raceHooks raceV hw [hl])
    let pendingAfter ← monadLift (Runtime.pending raceHooks)
    rWinnerRef.set rwinner
    rPendingBeforeRef.set pendingBefore
    rPendingAfterRef.set pendingAfter
    monadLift (IO.Promise.resolve (.ok ()) gRel : BaseIO Unit)
    let loserOutcome ← LeanIn.Task.EAsync.ofAsync (LeanIn.Task.Async.await hl)
    let loserFinal? ← monadLift (LeanIn.Task.Join.value? hl.cell)
    rLoserOutcomeRef.set (match loserOutcome with | .error _ => "error" | .ok _ => "ok")
    rLoserFinalRef.set (match loserFinal? with
      | some (.error _) => "error" | some (.ok _) => "ok" | none => "none")
  match ← Runtime.run raceE raceProg with
  | .error err => IO.println s!"race|failed={err}"; return 1
  | .ok () =>
    let rwinner ← rWinnerRef.get
    let pendingBefore ← rPendingBeforeRef.get
    let pendingAfter ← rPendingAfterRef.get
    let loserOutcome ← rLoserOutcomeRef.get
    let loserFinal ← rLoserFinalRef.get
    let raceSteps ← raceLog.atomically get
    let raceUs := (← IO.monoNanosNow) - raceStart
    let winnerRan := if raceSteps.contains "w-ran" then "yes" else "no"
    let loserRanOn := if raceSteps.contains "l-ran" then "yes" else "no"
    let winnerLabel := if rwinner == 0 then "w" else "l"
    let loserLabel := if rwinner == 0 then "l" else "w"
    IO.println s!"race|winner={winnerLabel}|loser={loserLabel}|loserOutcome={loserOutcome}|loserRanOn={loserRanOn}|pendingBefore={pendingBefore}|pendingAfter={pendingAfter}|winnerRan={winnerRan}|loserFinal={loserFinal}|runUs={raceUs / 1000}"
  -- PRIORITY
  let prioStart ← IO.monoNanosNow
  let k := 4
  let runA ← priorityRun k false
  let runB ← priorityRun k true
  let normalThenHigh := servedLabelOrder runA
  let highThenNormal := servedLabelOrder runB
  let servedBeforeHigh := servedBefore "high" runA
  let servedBeforeNormal := servedBefore "normal" runB
  let prioUs := (← IO.monoNanosNow) - prioStart
  IO.println s!"priority|k={k}|normalThenHigh={normalThenHigh}|highThenNormal={highThenNormal}|servedBeforeHigh={servedBeforeHigh}|servedBeforeNormal={servedBeforeNormal}|runUs={prioUs / 1000}"
  IO.println selectCtlLine
  -- MEASUREMENT (printed, never asserted): a select's cost against a plain await, a race's cost
  -- against a plain await, the priority order the argument changes, and enqueue-to-first-step.
  let benchN := 2000
  let benchE ← Sched.Executor.new LeanIn.Task.Item 256 1
  let benchHooks ← Runtime.Hooks.new
  let selBenchUs ← IO.mkRef (0 : Nat)
  let selAwaitUs ← IO.mkRef (0 : Nat)
  let raceBenchUs ← IO.mkRef (0 : Nat)
  let raceAwaitUs ← IO.mkRef (0 : Nat)
  let benchProg : LeanIn.Task.EAsync IO.Error Unit := do
    let h ← monadLift (resolvedTask (7 : Nat))
    let h2 ← monadLift (resolvedTask (8 : Nat))
    let t0 ← monadLift (IO.monoNanosNow : IO Nat)
    for _ in List.range benchN do
      let _ ← LeanIn.Task.EAsync.ofAsync (LeanIn.Task.select h [h2])
    let t1 ← monadLift (IO.monoNanosNow : IO Nat)
    selBenchUs.set (t1 - t0)
    let t2 ← monadLift (IO.monoNanosNow : IO Nat)
    for _ in List.range benchN do
      let _ ← LeanIn.Task.EAsync.ofAsync (LeanIn.Task.Async.await h)
    let t3 ← monadLift (IO.monoNanosNow : IO Nat)
    selAwaitUs.set (t3 - t2)
    let rw ← monadLift (resolvedTask (.ok () : Except IO.Error Unit))
    let t4 ← monadLift (IO.monoNanosNow : IO Nat)
    for _ in List.range benchN do
      let started ← monadLift (IO.Promise.new : IO (IO.Promise (Except IO.Error Unit)))
      let gate ← monadLift (IO.Promise.new : IO (IO.Promise (Except IO.Error Unit)))
      let lBody : LeanIn.Task.Async (Except IO.Error Unit) := do
        monadLift (IO.Promise.resolve (.ok ()) started : BaseIO Unit)
        let _ ← Runtime.awaitPromiseE benchHooks gate
        return .ok ()
      let hl ← LeanIn.Task.EAsync.ofAsync (LeanIn.Task.Async.spawn lBody)
      let _ ← Runtime.awaitPromiseE benchHooks started
      let _ ← LeanIn.Task.EAsync.ofAsync
        (Runtime.race benchHooks (.error (.userError "sc16")) rw [hl])
      pure ()
    let t5 ← monadLift (IO.monoNanosNow : IO Nat)
    raceBenchUs.set (t5 - t4)
    let t6 ← monadLift (IO.monoNanosNow : IO Nat)
    for _ in List.range benchN do
      let _ ← LeanIn.Task.EAsync.ofAsync (LeanIn.Task.Async.await rw)
    let t7 ← monadLift (IO.monoNanosNow : IO Nat)
    raceAwaitUs.set (t7 - t6)
  let _ ← Runtime.run benchE benchProg
  IO.println s!"selectbench|n={benchN}|selectUs={(← selBenchUs.get) / 1000}|awaitUs={(← selAwaitUs.get) / 1000}"
  IO.println s!"racebench|n={benchN}|raceUs={(← raceBenchUs.get) / 1000}|awaitUs={(← raceAwaitUs.get) / 1000}"
  IO.println s!"priorityorder|k={k}|normalThenHigh={normalThenHigh}|highThenNormal={highThenNormal}|servedBeforeHigh={servedBeforeHigh}|servedBeforeNormal={servedBeforeNormal}"
  let benchK := 4
  let benchRounds := 100
  let (highNs, normalNs) ← priorityBench benchK benchRounds
  IO.println s!"prioritybench|n={benchRounds}|k={benchK}|highUs={highNs / 1000}|normalUs={normalNs / 1000}"
  return 0

-- --- SC17 — the handle, a signal-driven drain, and a harness clock ————————————————————————————————

/-- The `handle|` record's fields, in the order the mode prints them. -/
def handleFields : List String :=
  ["spawnTid", "ranTid", "carrierTid", "readyBefore", "parkedBefore", "readyAfter", "parkedAfter",
   "runUs"]

/-- The `clock|` record's fields, in the order the mode prints them. -/
def clockFields : List String :=
  ["completesAt", "longDeadline", "longOutcome", "longElapsed", "shortDeadline", "shortOutcome",
   "shortElapsed", "pendingAfter", "deadlineAt", "deadlineWinner", "runUs"]

/-- The `signal|` record's fields, in the order the mode prints them. -/
def signalFields : List String :=
  ["signal", "signalSeen", "stopSeen", "handlerCarrier", "acceptedAtStop", "acceptedFinal",
   "offered", "bodyDone", "inFlightAfter", "pendingHooks", "listener", "log", "runUs"]

/-- The `tokens|` record's fields, in the order the mode prints them. -/
def tokensFields : List String :=
  ["sequential", "sequentialDistinct", "contended", "contendedDistinct"]

/-- The `handlectl|` record's fields, in the order the mode prints them. -/
def handleCtlFields : List String := ["accepted", "rejected", "variants"]

/-- The bracketed event log's relation: exactly one of each named event, `accept:1 < stop-observed <
body-echoed < drain-returned` and `stop-observed < offer:2`, and no `accept:2`. A missing, doubled or
misordered event is rejected before any position is compared. -/
def signalLogOk (v : String) : Bool :=
  if !(v.startsWith "[" && v.endsWith "]") then false
  else
    let body := ((v.drop 1).dropEnd 1).toString
    let evs := body.splitOn ","
    let idx (e : String) : Option Nat := evs.findIdx? (· == e)
    let once (e : String) : Bool := (evs.filter (· == e)).length == 1
    once "accept:1" && once "offer:2" && once "stop-observed" && once "body-echoed" &&
      once "drain-returned" && !(evs.contains "accept:2") &&
      (match idx "accept:1", idx "stop-observed", idx "body-echoed", idx "drain-returned",
             idx "offer:2" with
       | some a, some s, some b, some d, some o => a < s && s < b && b < d && s < o
       | _, _, _, _, _ => false)

/-- SC17-O1 as a detector: the spawned work ran on a carrier (`ranTid = carrierTid`) and not on the
thread that spawned it (`ranTid ≠ spawnTid`, `carrierTid ≠ spawnTid`), with the carrier parked when the
foreign spawn arrived (`parkedBefore = 1`, `readyBefore = 0`) and the run returning with nothing held
and nobody parked (`readyAfter = 0`, `parkedAfter = 0`). -/
def handleOk (rec : String) : Bool :=
  registryShaped rec handleFields &&
  match serviceNat rec "spawnTid", serviceNat rec "ranTid", serviceNat rec "carrierTid",
        serviceNat rec "readyBefore", serviceNat rec "parkedBefore", serviceNat rec "readyAfter",
        serviceNat rec "parkedAfter" with
  | some spawnTid, some ranTid, some carrierTid, some rb, some pb, some ra, some pa =>
      ranTid == carrierTid && ranTid != spawnTid && carrierTid != spawnTid &&
        pb == 1 && rb == 0 && ra == 0 && pa == 0
  | _, _, _, _, _, _, _ => false

/-- SC17-O2 as a detector: the delivered signal drove the shutdown (`signal = 15`, `signalSeen = yes`);
the stop was observed before the second offer; the loop stopped accepting (`acceptedFinal = 1` while
`offered = 2`, no `accept:2`); it had accepted the one offered before the stop (`acceptedAtStop = 1`,
the affirmative control); the connection in flight completed (`bodyDone = yes`, `drain-returned` last);
the drain returned with nothing held or outstanding (`inFlightAfter = 0`, `pendingHooks = 0`); the
handler step ran on a carrier (`handlerCarrier = yes`); and the socket outlived its last use
(`listener` nonempty). -/
def signalOk (rec : String) : Bool :=
  registryShaped rec signalFields &&
  match serviceNat rec "signal", serviceField rec "signalSeen", serviceField rec "stopSeen",
        serviceField rec "handlerCarrier", serviceNat rec "acceptedAtStop",
        serviceNat rec "acceptedFinal", serviceNat rec "offered", serviceField rec "bodyDone",
        serviceNat rec "inFlightAfter", serviceNat rec "pendingHooks", serviceField rec "listener",
        serviceField rec "log" with
  | some signal, some signalSeen, some stopSeen, some handlerCarrier, some acceptedAtStop,
    some acceptedFinal, some offered, some bodyDone, some inFlightAfter, some pendingHooks,
    some listener, some log =>
      signal == 15 && signalSeen == "yes" && stopSeen == "yes" && handlerCarrier == "yes" &&
        acceptedAtStop == 1 && acceptedFinal == 1 && offered == 2 && bodyDone == "yes" &&
        inFlightAfter == 0 && pendingHooks == 0 && listener != "" && signalLogOk log
  | _, _, _, _, _, _, _, _, _, _, _, _ => false

/-- SC17-O3 as a detector: the longer deadline did not trip and the harness clock says so
(`longOutcome = some:7`, `longElapsed = completesAt`); the shorter deadline — proved shorter — tripped
(`shortDeadline < completesAt`, `shortOutcome = none`, `shortElapsed = shortDeadline`); the run ended
without advancing to the loser (`pendingAfter = 1`); and a deadline raced against a timer handle is
decided at the stated instant (`deadlineWinner = timer`, `deadlineAt = completesAt`). -/
def clockOk (rec : String) : Bool :=
  registryShaped rec clockFields &&
  match serviceNat rec "completesAt", serviceField rec "longOutcome", serviceNat rec "longElapsed",
        serviceNat rec "shortDeadline", serviceField rec "shortOutcome", serviceNat rec "shortElapsed",
        serviceNat rec "pendingAfter", serviceNat rec "deadlineAt", serviceField rec "deadlineWinner" with
  | some completesAt, some longOutcome, some longElapsed, some shortDeadline, some shortOutcome,
    some shortElapsed, some pendingAfter, some deadlineAt, some deadlineWinner =>
      longOutcome == "some:7" && longElapsed == completesAt &&
        shortDeadline < completesAt && shortOutcome == "none" && shortElapsed == shortDeadline &&
        pendingAfter == 1 && deadlineWinner == "timer" && deadlineAt == completesAt
  | _, _, _, _, _, _, _, _, _ => false

/-- The token-id control as a detector: the sequential reading (`n` distinct ids out of `n`, sound on
any correct allocator) and the contended reading (all ids distinct, sound because the allocator's
read-modify-write is inside a critical section). -/
def tokensOk (rec : String) : Bool :=
  registryShaped rec tokensFields &&
  match serviceNat rec "sequential", serviceNat rec "sequentialDistinct", serviceNat rec "contended",
        serviceNat rec "contendedDistinct" with
  | some seq, some seqD, some con, some conD => seq == seqD && con == conD
  | _, _, _, _ => false

/-- A well-formed `handle|` record, built from the record syntax and the expectation rather than from
the mode's output, so the checker's controls cannot agree with the mode by construction. -/
def handleGoodRec : String :=
  "spawnTid=100|ranTid=200|carrierTid=200|readyBefore=0|parkedBefore=1|readyAfter=0|parkedAfter=0|runUs=1"

/-- The work ran on the calling thread: a `Handle.spawn` that fires its item where it stands. -/
def handleNearCaller : String := handleGoodRec.replace "ranTid=200" "ranTid=100"

/-- A well-formed `clock|` record, likewise. -/
def clockGoodRec : String :=
  "completesAt=30|longDeadline=100|longOutcome=some:7|longElapsed=30|shortDeadline=20|shortOutcome=none|shortElapsed=20|pendingAfter=1|deadlineAt=30|deadlineWinner=timer|runUs=1"

/-- The harness clock never advanced: every timer fired at instant zero. -/
def clockNearElapsed : String := clockGoodRec.replace "longElapsed=30" "longElapsed=0"

/-- A well-formed `signal|` record, likewise. -/
def signalGoodRec : String :=
  "signal=15|signalSeen=yes|stopSeen=yes|handlerCarrier=yes|acceptedAtStop=1|acceptedFinal=1|offered=2|bodyDone=yes|inFlightAfter=0|pendingHooks=0|listener=127.0.0.1:1|log=[accept:1,stop-observed,body-echoed,drain-returned,offer:2]|runUs=1"

/-- A connection offered after the stop was accepted. -/
def signalNearAccepted : String := signalGoodRec.replace "acceptedFinal=1" "acceptedFinal=2"

/-- A well-formed `tokens|` record, likewise. -/
def tokensGoodRec : String := "sequential=8|sequentialDistinct=8|contended=8|contendedDistinct=8"

/-- A duplicate token id was handed out. -/
def tokensNearDuplicate : String := tokensGoodRec.replace "sequentialDistinct=8" "sequentialDistinct=7"

/-- The calling OS thread's id, as a natural, for the records that compare tids. -/
def currentTid : IO Nat := do return (← IO.getTID).toNat

/-- The mode's own checker readings: `accepted=yes` when the well-formed record set is accepted,
`rejected=yes` when every near miss is rejected, and `variants=4`, the number of near-miss variants
tested — one per clause plus the token-id control. -/
def handleCtlLine : String :=
  "handlectl|accepted=" ++
    (if handleOk handleGoodRec && signalOk signalGoodRec && clockOk clockGoodRec &&
        tokensOk tokensGoodRec then "yes" else "no") ++
  "|rejected=" ++
    (if !(handleOk handleNearCaller) && !(signalOk signalNearAccepted) &&
        !(clockOk clockNearElapsed) && !(tokensOk tokensNearDuplicate) then "yes" else "no") ++
  "|variants=4"

/-- **SC17 — a handle spawns onto a running executor, a signal stops then drains, and timeouts are read
from a harness clock.**

One invocation prints the `handle|`, `clock|`, `signal|` and `tokens|` records, the mode's own
`handlectl|` checker readings, and three measurement rows printed and never asserted.

Diagnostic: `lake exe controls --runtime-handle [--ready-file PATH]`. -/
def runtimeHandle (readyFile : String) : IO UInt32 := do
  let completesAtMs : Std.Time.Millisecond.Offset := 30
  let longDeadlineMs : Std.Time.Millisecond.Offset := 100
  let shortDeadlineMs : Std.Time.Millisecond.Offset := 20
  let completesAt : Nat := completesAtMs.val.toNat
  let longDeadline : Nat := longDeadlineMs.val.toNat
  let shortDeadline : Nat := shortDeadlineMs.val.toNat
  -- ================= clause one: a handle spawns from a thread that is not a carrier =================
  let hStart ← IO.monoNanosNow
  let e1 ← Sched.Executor.new LeanIn.Task.Item 256 1
  let h1 := Runtime.handle e1
  let gate1 ← (LeanIn.Task.Join.new : IO (LeanIn.Task.Join Unit))
  let gate1Tok ← LeanIn.Task.Cancel.new
  let carrierTidRef ← IO.mkRef (0 : Nat)
  let prog1 : LeanIn.Task.Async Unit := do
    let tid0 ← monadLift currentTid
    monadLift (carrierTidRef.set tid0 : IO Unit)
    let _ ← LeanIn.Task.Async.await (show LeanIn.Task.Task Unit from ⟨gate1, gate1Tok⟩)
    pure ()
  let carrier1 ← IO.asTask (Runtime.run e1 prog1) _root_.Task.Priority.dedicated
  let mut parkedBefore := 0
  let mut readyBefore := 0
  let mut sawParked := false
  let mut pSpins := 0
  while !sawParked && pSpins < 200000 do
    let m ← Runtime.Handle.metrics h1
    if m.parked == 1 && m.ready == 0 then
      parkedBefore := m.parked
      readyBefore := m.ready
      sawParked := true
    else
      IO.sleep 1
      pSpins := pSpins + 1
  let spawnTid ← currentTid
  let carrierTid ← carrierTidRef.get
  let ranTidRef ← IO.mkRef (0 : Nat)
  let spawned1 : LeanIn.Task.Async Unit := do
    let tid0 ← monadLift currentTid
    monadLift (ranTidRef.set tid0 : IO Unit)
    let push ← LeanIn.Task.Async.push
    monadLift (LeanIn.Task.Join.resolve gate1 push () : IO Unit)
  let _ ← Runtime.Handle.spawn h1 Runtime.Priority.normal spawned1
  let _ ← IO.wait carrier1
  let ranTid ← ranTidRef.get
  let m1 ← Runtime.Handle.metrics h1
  let hUs := (← IO.monoNanosNow) - hStart
  IO.println s!"handle|spawnTid={spawnTid}|ranTid={ranTid}|carrierTid={carrierTid}|readyBefore={readyBefore}|parkedBefore={parkedBefore}|readyAfter={m1.ready}|parkedAfter={m1.parked}|runUs={hUs / 1000}"
  -- ================= clause three: a timeout at a stated instant, read from the harness clock =================
  let cStart ← IO.monoNanosNow
  let e3 ← Sched.Executor.new LeanIn.Task.Item 256 1
  let hcA ← Runtime.HarnessClock.new
  let cA := Runtime.HarnessClock.clock hcA
  let beforeA ← Runtime.HarnessClock.now hcA
  let longOutcome ← Runtime.runVirtual hcA e3
    (Runtime.withTimeout cA longDeadlineMs (do Runtime.sleep cA completesAtMs; pure (7 : Nat)))
  let afterA ← Runtime.HarnessClock.now hcA
  let longElapsed := afterA - beforeA
  let hcB ← Runtime.HarnessClock.new
  let cB := Runtime.HarnessClock.clock hcB
  let beforeB ← Runtime.HarnessClock.now hcB
  let shortOutcome ← Runtime.runVirtual hcB e3
    (Runtime.withTimeout cB shortDeadlineMs (do Runtime.sleep cB completesAtMs; pure (7 : Nat)))
  let afterB ← Runtime.HarnessClock.now hcB
  let shortElapsed := afterB - beforeB
  let pendingAfter ← Runtime.HarnessClock.pending hcB
  let hcC ← Runtime.HarnessClock.new
  let cC := Runtime.HarnessClock.clock hcC
  let hooks3 ← Runtime.Hooks.new
  let gate3 ← (IO.Promise.new : IO (IO.Promise (Except IO.Error Unit)))
  let deadlineAtRef ← IO.mkRef (0 : Nat)
  let deadlineWinnerRef ← IO.mkRef "timer"
  let arm3 : LeanIn.Task.EAsync IO.Error Unit := do
    let timerH ← monadLift (Runtime.spawn e3 Runtime.Priority.normal (Runtime.sleep cC completesAtMs))
    let reqBody : LeanIn.Task.Async Unit := do
      let _ ← Runtime.awaitPromiseE hooks3 gate3
      pure ()
    let reqH ← monadLift (Runtime.spawn e3 Runtime.Priority.normal reqBody)
    let (i, _v) ← LeanIn.Task.EAsync.ofAsync (LeanIn.Task.select timerH [reqH])
    let dt ← monadLift (Runtime.HarnessClock.now hcC)
    monadLift (deadlineAtRef.set dt : IO Unit)
    monadLift (deadlineWinnerRef.set (if i == 0 then "timer" else "request") : IO Unit)
    pure ()
  let _ ← Runtime.runVirtual hcC e3 arm3
  let deadlineAt ← deadlineAtRef.get
  let deadlineWinner ← deadlineWinnerRef.get
  let cUs := (← IO.monoNanosNow) - cStart
  let longStr := match longOutcome with | some v => s!"some:{v}" | none => "none"
  let shortStr := match shortOutcome with | some v => s!"some:{v}" | none => "none"
  IO.println s!"clock|completesAt={completesAt}|longDeadline={longDeadline}|longOutcome={longStr}|longElapsed={longElapsed}|shortDeadline={shortDeadline}|shortOutcome={shortStr}|shortElapsed={shortElapsed}|pendingAfter={pendingAfter}|deadlineAt={deadlineAt}|deadlineWinner={deadlineWinner}|runUs={cUs / 1000}"
  -- ================= clause two: a registered signal stops accepting, then drains =================
  let sStart ← IO.monoNanosNow
  let hooks2 ← Runtime.Hooks.new
  let e2 ← Sched.Executor.new LeanIn.Task.Item 256 1
  let h2 := Runtime.handle e2
  let l ← Runtime.Listener.bind (Runtime.loopback 0)
  let acceptedMu ← Std.Mutex.new (0 : Nat)
  let logMu ← Std.Mutex.new ([] : List String)
  let bodyDoneMu ← Std.Mutex.new false
  let acceptedAtStopRef ← IO.mkRef (0 : Nat)
  let stopSeenRef ← IO.mkRef false
  let signalValRef ← IO.mkRef (0 : Int)
  let carrierTid2Ref ← IO.mkRef (0 : Nat)
  let handlerTidRef ← IO.mkRef (0 : Nat)
  let stopAtRef ← IO.mkRef (0 : Nat)
  let drainAtRef ← IO.mkRef (0 : Nat)
  let gate ← (IO.Promise.new : IO (IO.Promise (Except IO.Error Unit)))
  let stopP ← (IO.Promise.new : IO (IO.Promise (Except IO.Error Unit)))
  let addrRef ← IO.mkRef (none : Option Std.Net.SocketAddress)
  let payload : ByteArray := "sc17-signal".toUTF8
  let logMod (f : List String → List String) : IO Unit := logMu.atomically do set (f (← get))
  let bump : IO Unit := acceptedMu.atomically do set ((← get) + 1)
  let readAccepted : IO Nat := acceptedMu.atomically get
  let body (c : Runtime.Conn) : LeanIn.Task.EAsync IO.Error Unit := do
    monadLift (bump : IO Unit)
    monadLift (logMod (fun s => s ++ ["accept:1"]) : IO Unit)
    let _ ← Runtime.awaitPromiseE hooks2 gate
    let _ ← Runtime.Conn.send c hooks2 payload
    let _ ← Runtime.Conn.shutdown c hooks2
    monadLift (logMod (fun s => s ++ ["body-echoed"]) : IO Unit)
    monadLift (bodyDoneMu.atomically do set true : IO Unit)
  let prog2 : LeanIn.Task.EAsync IO.Error Unit := do
    let cTid ← monadLift currentTid
    monadLift (carrierTid2Ref.set cTid : IO Unit)
    let sa ← monadLift (Runtime.Listener.sockName l)
    monadLift (addrRef.set (some sa) : IO Unit)
    let loopH ← LeanIn.Task.EAsync.ofAsync
      (LeanIn.Task.Async.spawn (Runtime.serveUntilStopped hooks2 e2 l 1 body []))
    let sig ← LeanIn.Task.EAsync.ofAsync (Runtime.awaitSignal hooks2 .sigterm false)
    let hTid ← monadLift currentTid
    monadLift (handlerTidRef.set hTid : IO Unit)
    monadLift (signalValRef.set sig : IO Unit)
    monadLift (logMod (fun s => s ++ ["stop-observed"]) : IO Unit)
    monadLift (stopSeenRef.set true : IO Unit)
    monadLift (h2.stop : IO Unit)
    let now0 ← monadLift (IO.monoNanosNow : IO Nat)
    monadLift (stopAtRef.set now0 : IO Unit)
    let acc0 ← monadLift readAccepted
    monadLift (acceptedAtStopRef.set acc0 : IO Unit)
    monadLift (IO.Promise.resolve (.ok ()) gate : BaseIO Unit)
    monadLift (IO.Promise.resolve (.ok ()) stopP : BaseIO Unit)
    let _ ← LeanIn.Task.EAsync.ofAsync (LeanIn.Task.Async.await loopH)
    let now1 ← monadLift (IO.monoNanosNow : IO Nat)
    monadLift (drainAtRef.set now1 : IO Unit)
    monadLift (logMod (fun s => s ++ ["drain-returned"]) : IO Unit)
  let server2 ← IO.asTask (Runtime.run e2 prog2) _root_.Task.Priority.dedicated
  let addr ← do
    let mut a : Option Std.Net.SocketAddress := none
    let mut aSpins := 0
    while a.isNone && aSpins < 200000 do
      a ← addrRef.get
      if a.isNone then IO.sleep 1; aSpins := aSpins + 1
    pure (a.getD (Runtime.loopback 0))
  let socks ← IO.mkRef ([] : List Std.Async.TCP.Socket.Client)
  let offeredRef ← IO.mkRef (0 : Nat)
  let first ← Std.Async.Async.block do
    let c ← Std.Async.TCP.Socket.Client.mk
    c.connect addr
    c.send payload
    return c
  socks.set [first]
  offeredRef.modify (· + 1)
  let mut firstSeen := false
  let mut fSpins := 0
  while !firstSeen && fSpins < 200000 do
    let acc ← acceptedMu.atomically get
    let st ← IO.getTaskState server2
    if acc >= 1 || st == .finished then firstSeen := true
    else IO.sleep 1; fSpins := fSpins + 1
  if readyFile != "" then
    IO.FS.writeFile readyFile (toString (← IO.Process.getPID))
  let mut stopObserved := false
  let mut bSpins := 0
  while !stopObserved && bSpins < 600000 do
    if ← IO.Promise.isResolved stopP then stopObserved := true
    else IO.sleep 1; bSpins := bSpins + 1
  let second ← Std.Async.Async.block do
    let c ← Std.Async.TCP.Socket.Client.mk
    c.connect addr
    c.send payload
    c.shutdown
    return c
  socks.modify (· ++ [second])
  offeredRef.modify (· + 1)
  logMod (fun s => s ++ ["offer:2"])
  let outcome2 ← IO.wait server2
  let acceptedFinal ← acceptedMu.atomically get
  let offered ← offeredRef.get
  let bodyDone ← bodyDoneMu.atomically get
  let (inFlightAfter, _) ← e2.observe
  let pendingHooks ← Runtime.pending hooks2
  let stillBound ← Runtime.Listener.sockName l
  let log ← logMu.atomically get
  let signalVal ← signalValRef.get
  let carrierTid2 ← carrierTid2Ref.get
  let handlerTid ← handlerTidRef.get
  let acceptedAtStop ← acceptedAtStopRef.get
  let stopSeen ← stopSeenRef.get
  let sUs := (← IO.monoNanosNow) - sStart
  let stopToDrain := (← drainAtRef.get) - (← stopAtRef.get)
  let _keep := (← socks.get)
  let signalSeen := if signalVal == (15 : Int) then "yes" else "no"
  let stopSeenStr := if stopSeen then "yes" else "no"
  let handlerCarrier := if handlerTid == carrierTid2 then "yes" else "no"
  let bodyDoneStr := if bodyDone then "yes" else "no"
  IO.println s!"signal|signal={signalVal}|signalSeen={signalSeen}|stopSeen={stopSeenStr}|handlerCarrier={handlerCarrier}|acceptedAtStop={acceptedAtStop}|acceptedFinal={acceptedFinal}|offered={offered}|bodyDone={bodyDoneStr}|inFlightAfter={inFlightAfter}|pendingHooks={pendingHooks}|listener={stillBound}|log=[{String.intercalate "," log}]|runUs={sUs / 1000}"
  IO.println s!"signaldrain|pollMs=1|stopToDrainUs={stopToDrain / 1000}|accepted={acceptedFinal}|offered={offered}"
  match outcome2 with
  | .error err => IO.println s!"signalerr|run={err}"
  | .ok (.error err) => IO.println s!"signalerr|program={err}"
  | .ok (.ok ()) => pure ()
  -- ================= the token-id control =================
  let tokensE ← Sched.Executor.new LeanIn.Task.Item 256 1
  let tokensH := Runtime.handle tokensE
  let seqN := 64
  let mut seqIds : List Nat := []
  for _ in List.range seqN do
    let t ← Runtime.Handle.spawn tokensH Runtime.Priority.normal (pure () : LeanIn.Task.Async Unit)
    seqIds := t.token.id :: seqIds
  let sequential := seqIds.length
  let sequentialDistinct := seqIds.eraseDups.length
  let contN := 64
  let collectIds (k : Nat) : IO (List Nat) := do
    let mut ids : List Nat := []
    for _ in List.range k do
      let t ← Runtime.Handle.spawn tokensH Runtime.Priority.normal (pure () : LeanIn.Task.Async Unit)
      ids := t.token.id :: ids
    return ids
  let ta ← IO.asTask (collectIds contN) _root_.Task.Priority.dedicated
  let tb ← IO.asTask (collectIds contN) _root_.Task.Priority.dedicated
  let ra ← IO.wait ta
  let rb ← IO.wait tb
  let ca := match ra with | .ok ids => ids | .error _ => ([] : List Nat)
  let cb := match rb with | .ok ids => ids | .error _ => ([] : List Nat)
  let contendedIds := ca ++ cb
  let contended := contendedIds.length
  let contendedDistinct := contendedIds.eraseDups.length
  IO.println s!"tokens|sequential={sequential}|sequentialDistinct={sequentialDistinct}|contended={contended}|contendedDistinct={contendedDistinct}"
  -- ================= measurement rows, printed and never asserted =================
  let benchN := 200
  let hbE ← Sched.Executor.new LeanIn.Task.Item 256 1
  let hbH := Runtime.handle hbE
  let hbGate ← (LeanIn.Task.Join.new : IO (LeanIn.Task.Join Unit))
  let hbTok ← LeanIn.Task.Cancel.new
  let hbProg : LeanIn.Task.Async Unit := do
    let _ ← LeanIn.Task.Async.await (show LeanIn.Task.Task Unit from ⟨hbGate, hbTok⟩)
    pure ()
  let hbCarrier ← IO.asTask (Runtime.run hbE hbProg) _root_.Task.Priority.dedicated
  let mut hbParked := false
  let mut hbSpins := 0
  while !hbParked && hbSpins < 200000 do
    let m ← Runtime.Handle.metrics hbH
    if m.parked == 1 then hbParked := true else IO.sleep 1; hbSpins := hbSpins + 1
  let hbT0 ← IO.monoNanosNow
  for _ in List.range benchN do
    let _ ← Runtime.Handle.spawn hbH Runtime.Priority.normal (pure () : LeanIn.Task.Async Unit)
  let hbT1 ← IO.monoNanosNow
  -- The resolution is made by this thread, which is not a carrier: the shared route is the one it can take,
  -- and its push unparks the parked driver under the shared cell's own lock.
  LeanIn.Task.Join.resolve hbGate (Runtime.sharedPush hbE) ()
  let _ ← IO.wait hbCarrier
  let spawnUs := (hbT1 - hbT0) / benchN / 1000
  let hbE2 ← Sched.Executor.new LeanIn.Task.Item 256 1
  let hbProg2 : LeanIn.Task.Async Nat := do
    let t0 ← monadLift (IO.monoNanosNow : IO Nat)
    for _ in List.range benchN do
      let _ ← monadLift (Runtime.spawn hbE2 Runtime.Priority.normal (pure () : LeanIn.Task.Async Unit))
      pure ()
    let t1 ← monadLift (IO.monoNanosNow : IO Nat)
    return t1 - t0
  let enqNs ← Runtime.run hbE2 hbProg2
  let wakeUs := enqNs / benchN / 1000
  IO.println s!"handlebench|n={benchN}|spawnUs={spawnUs}|wakeUs={wakeUs}"
  let mcN := 10000
  let plainE ← Sched.Executor.new LeanIn.Task.Item 256 1
  let meteredE ← Runtime.Executor.newMetered 256 1
  let mcRun : Sched.Executor LeanIn.Task.Item 256 → Nat → IO Nat := fun e n => do
    let hooks ← Runtime.Hooks.new
    let done ← (IO.Promise.new : IO (IO.Promise (Except IO.Error Unit)))
    let cnt ← Std.Mutex.new (0 : Nat)
    let bump : IO Nat := cnt.atomically do
      let k ← get
      set (k + 1)
      return k
    let body : LeanIn.Task.Async Unit := do
      let c ← monadLift bump
      if c + 1 == n then monadLift (IO.Promise.resolve (.ok ()) done : BaseIO Unit)
      pure ()
    let prog : LeanIn.Task.EAsync IO.Error Unit := do
      for _ in List.range n do
        let _ ← monadLift (Runtime.spawn e Runtime.Priority.normal body)
        pure ()
      let _ ← Runtime.awaitPromiseE hooks done
      pure ()
    let t0 ← IO.monoNanosNow
    let _ ← Runtime.run e prog
    return (← IO.monoNanosNow) - t0
  let mcRounds := 5
  let mut plainMin := 0
  let mut plainMax := 0
  let mut meteredMin := 0
  let mut meteredMax := 0
  for r in List.range mcRounds do
    -- Both arms run the same program at the same item count, on executors built the same way except that one is
    -- metered; the order alternates so a drift across the invocation cannot be read as the metering, and each
    -- arm's reading is its minimum over the rounds.
    let (mNs, pNs) ←
      if r % 2 == 0 then do
        let m ← mcRun meteredE mcN
        let p ← mcRun plainE mcN
        pure (m, p)
      else do
        let p ← mcRun plainE mcN
        let m ← mcRun meteredE mcN
        pure (m, p)
    if r == 0 then
      plainMin := pNs; plainMax := pNs; meteredMin := mNs; meteredMax := mNs
    else
      plainMin := Nat.min plainMin pNs; plainMax := Nat.max plainMax pNs
      meteredMin := Nat.min meteredMin mNs; meteredMax := Nat.max meteredMax mNs
  IO.println s!"metricscost|n={mcN}|rounds={mcRounds}|meteredUs={meteredMin / 1000}|plainUs={plainMin / 1000}|meteredMaxUs={meteredMax / 1000}|plainMaxUs={plainMax / 1000}"
  IO.println handleCtlLine
  return 0

/-- The `carriers|` record's fields, in the order the mode prints them. -/
def carriersFields : List String :=
  ["carriers", "p", "carrierTids", "ranTids", "distinctCarriers", "carrierCount1", "chainCarriers", "parkedBefore",
   "readyBefore", "ranTid", "spawnTid", "inWorkerTids", "wokeRounds", "ran1", "ran2", "parkedAfter",
   "readyAfter", "inFlightAfter", "pendingHooks", "scaleN", "remaining", "runUs"]

/-- The `steal|` record's fields, in the order the mode prints them. -/
def stealFields : List String :=
  ["victimRingBefore", "victimSlotBefore", "stolen", "victimRingAfter", "victimSlotAfter", "stolenFromEmpty",
   "emptyVictimRingBefore", "slotStolen", "slotVictimSlotBefore", "thiefRingAfter", "thiefSlotAfter", "thiefTid", "victimTid"]

/-- SC18-O1 and SC18-O3 as one detector: work spread over more than one of the *started* carriers, the same
detector reading exactly one on the `P = 1` arm, the chain's `chainCarriers` bound by its own named field and
compared in no clause, every carrier parked with nothing ready before a push from a thread that is not a
carrier, both pushes running on a carrier rather than
on the spawning thread, and the drain leaving nothing held. Every operand is read from its own named field.

The record's `carriers` field — the number of carriers the entry actually started, `Carriers.count` — is
shape-checked but is deliberately **not** one of O1's bindings: under the staged entry it reads `0`, and what
makes O1 fail is the relation `ranTids ⊆ carrierTids` (the caller's tid is in `ranTids` and `carrierTids` is
empty), not this count. -/
def carriersOk (rec : String) : Bool :=
  registryShaped rec carriersFields &&
  match serviceNat rec "p", serviceNat rec "distinctCarriers", serviceNat rec "carrierCount1",
        serviceNat rec "chainCarriers", serviceNat rec "parkedBefore", serviceNat rec "readyBefore",
        serviceNat rec "wokeRounds", serviceNat rec "parkedAfter", serviceNat rec "readyAfter",
        serviceNat rec "inFlightAfter", serviceNat rec "pendingHooks", serviceNat rec "scaleN",
        serviceNat rec "remaining", serviceNat rec "ranTid", serviceNat rec "spawnTid",
        serviceField rec "inWorkerTids", serviceField rec "ran1", serviceField rec "ran2",
        serviceIds rec "ranTids", serviceIds rec "carrierTids" with
  | some p, some dc, some cc1, some _chain, some pb, some rb, some _, some _, some _, some ifa, some pend,
    some sn, some rem, some ranTid, some spawnTid, some inw, some ran1, some ran2, some ranTids,
    some carrierTids =>
      dc ≥ 2 && cc1 == 1 && pb == p && rb == 0 && inw == "yes" &&
      ran1 == "yes" && ran2 == "yes" && ranTid ≠ spawnTid &&
      ranTids.all (fun t => carrierTids.contains t) &&
      ifa == 0 && pend == 0 && sn == 100000 && rem == 0
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => false

/-- SC18-O2 as a detector: the thief took exactly one item, from the victim's ring — one fewer there, and the
slot-only victim's slot read the same before and after — with the same call reading zero on an empty victim,
and `slotStolen` reading `no` while the slot-only victim's slot was occupied (`slotVictimSlotBefore = some`), so
the `no` cannot be vacuous. Every operand is read from its own named field. -/
def stealOk (rec : String) : Bool :=
  registryShaped rec stealFields &&
  match serviceNat rec "victimRingBefore", serviceNat rec "stolen", serviceNat rec "victimRingAfter",
        serviceNat rec "stolenFromEmpty", serviceNat rec "emptyVictimRingBefore",
        serviceNat rec "thiefRingAfter",
        serviceField rec "victimSlotBefore", serviceField rec "victimSlotAfter",
        serviceField rec "thiefSlotAfter", serviceField rec "slotStolen",
        serviceField rec "slotVictimSlotBefore" with
  | some vb, some stolen, some va, some sfe, some evb, some tra, some vsb, some vsa, some tsa, some ss,
    some svsb =>
      vb ≥ 1 && stolen == 1 && va + 1 == vb && sfe == 0 && evb == 0 && tra == 0 &&
      vsa == vsb && tsa == "-" && ss == "no" && svsb == "some"
  | _, _, _, _, _, _, _, _, _, _, _ => false

/-- A well-formed `carriers|` record, built from the record syntax and the expectation rather than from the
mode's output, so the detector's controls cannot agree with the mode by construction. -/
def carriersGoodRec : String :=
  "carriers=4|p=4|carrierTids=[10,11,12,13]|ranTids=[10,11]|distinctCarriers=2|carrierCount1=1|chainCarriers=1|parkedBefore=4|readyBefore=0|ranTid=10|spawnTid=9|inWorkerTids=yes|wokeRounds=3|ran1=yes|ran2=yes|parkedAfter=0|readyAfter=0|inFlightAfter=0|pendingHooks=0|scaleN=100000|remaining=0|runUs=1"

/-- The work ran on the calling thread: a push that fires its item where it stands. -/
def carriersNearCaller : String := carriersGoodRec.replace "ranTid=10|" "ranTid=9|"

/-- A chain observed across carriers: the structural half of the chain condition. -/
def carriersNearChain : String := carriersGoodRec.replace "chainCarriers=1" "chainCarriers=2"

/-- A well-formed `steal|` record, likewise. -/
def stealGoodRec : String :=
  "victimRingBefore=200|victimSlotBefore=-|stolen=1|victimRingAfter=199|victimSlotAfter=-|stolenFromEmpty=0|emptyVictimRingBefore=0|slotStolen=no|slotVictimSlotBefore=some|thiefRingAfter=0|thiefSlotAfter=-|thiefTid=9|victimTid=9"

/-- A thief that kept a batch: the ring lost two while the take is counted once. -/
def stealNearBatch : String :=
  stealGoodRec.replace "victimRingAfter=199" "victimRingAfter=198"

/-- The slot-only victim's slot was cleared by the call: the shape a slot-taking thief produces. -/
def stealNearSlot : String := stealGoodRec.replace "slotStolen=no" "slotStolen=yes"

/-- The mode's own checker readings: the accepted set is three records rather than a pair — the well-formed
pair plus the chain record, which the route rebinding makes an acceptance rather than a near miss — each
remaining near miss is rejected, and `variants` is derived as `near.length`, the number of near-miss variants
exercised: the caller, clause two's batch, and the slot-cleared record.

**A description, not evidence.** The mode evaluates its own `carriersOk`/`stealOk` on records it constructs
so that they pass by construction, so this line states *what the fixture is expected to exercise*; it is not a
reading of the system and nothing takes it for one. The authority for the near-miss rejections is the shell
fixture's own exercises (`tests/executor-contract.sh`, whose `setup_error` paths reject each near miss), and
`check_sc18` re-derives the same accept/reject decisions from the record syntax independently. The `sendctl|`
line is likewise a description: `unmarkedPushes` is printed as the constant `0` the marked path makes true,
and the marker's real enforcement is the compile (an unmarked push does not elaborate), not this line. -/
def carriersCtlLine : String :=
  let good := [carriersOk carriersGoodRec, stealOk stealGoodRec, carriersOk carriersNearChain]
  let near := [carriersOk carriersNearCaller, stealOk stealNearBatch, stealOk stealNearSlot]
  "carriersctl|accepted=" ++ (if good.all id then "yes" else "no") ++
  "|rejected=" ++ (if near.all (fun b => !b) then "yes" else "no") ++
  "|variants=" ++ toString near.length

/-- The box's logical core count, read for the batch row so that oversubscription at the widest arm is
visible rather than mysterious: the native pool's own width is a configuration, and a `ratio` that reverses
at the widest arm on a box narrower than that width is a property of the box and not of the queue. A box
without `/proc/cpuinfo` reports `0`, which the row prints as `-`. -/
def boxCores : IO Nat := do
  try
    let s ← IO.FS.readFile "/proc/cpuinfo"
    let mut n := 0
    for l in s.splitOn "\n" do
      if String.startsWith l "processor" then n := n + 1
    return n
  catch _ => return 0

/-- **SC18 — the carriers, the thief, and a wake from a thread that is not a carrier.**

Three clauses over one invocation, each with its affirmative control in the same run. Clause one: the mode
calls the multi-carrier entry `Runtime.runCarriers e p program` — one shape — and the mode's own thread, which
is **not** a carrier, waits on the program's cell; the detector compares the tids that ran with the carriers'
own recorded tids, and the same program and detector at `P = 1` is the affirmative control that reads a single
carrier. Clause two:
this thread drives one public steal against a victim whose ring holds and reads that victim's ring and slot
around it, with an empty victim and a slot-only victim as the controls. Clause three: with every carrier parked and
nothing ready, this thread pushes through the capability an off-carrier thread gets and the pushed computation
runs on a carrier; a second push shows one wake is not a single-shot accident, and the drain leaves nothing
held. The scale arm is the same wake at `n = 100000`.

The steal record's ring and slot fields describe the ring victim, its `stolen`/`stolenFromEmpty` the two calls
against the ring victim and the empty worker, `slotStolen` the call against the slot-only victim — computed from
that victim's slot occupancy before and after, and `no` exactly when the slot was occupied and is still occupied
after, which `slotVictimSlotBefore` records — and `thiefRingAfter`/`thiefSlotAfter` the thief's own pool after
the steal, so a thief that took more from a ring than the take it counted is readable there. `thiefTid` is this
thread's — it drove the steal — and `victimTid` is the same thread's, because the prelude drove the victim's own
worker on it and no carrier has run there.

Every wait is a round count bounded by `--bound` — no assertion reads a clock, and `runUs` is printed and
never asserted. The three rows are the measurement conditions and are printed rather than asserted as well:
a timing assertion is a flake with a schedule.

Diagnostic: `lake exe controls --runtime-carriers [--workers P] [--bound N]`. -/
def runtimeCarriers (p bound : Nat) : IO UInt32 := do
  let p := max 1 p
  let runStart ← IO.monoNanosNow
  let spawnTid ← IO.getTID
  let n := 2048
  let scaleN := 100000
  let tidsText (ts : List UInt64) : String :=
    "[" ++ String.intercalate "," (ts.map toString) ++ "]"
  let slotText (s : Option Nat) : String :=
    match s with
    | some _ => "some"
    | none   => "-"
  let awaitRounds (j : LeanIn.Task.Join Unit) : IO (Bool × Nat) := do
    let mut seen := false
    let mut rounds := 0
    while !seen && rounds < bound do
      seen := (← LeanIn.Task.Join.value? j).isSome
      if !seen then rounds := rounds + 1
    return (seen, rounds)
  -- Progress on stderr, one line per stage with the milliseconds since the run began: this mode's arms are
  -- long — the shared list's cost at `scaleN` is the row's own subject — and a reader of a slow run should be
  -- able to see which stage it is in without the records being polluted.
  let stage (name : String) : IO Unit := do
    let now ← IO.monoNanosNow
    IO.eprintln s!"SC18 stage {name} at {(now - runStart) / 1000000}ms"
  -- `fanOutPush` runs a program on `workers` carriers with no driver: the carriers are started, the program is
  -- pushed through the off-carrier capability — the shared list, the one queue a thread that is not a carrier
  -- can reach — and the cell it resolves is awaited by a bounded round count, then the carriers are stopped and
  -- joined. It is the shape the *unasserted rows* use: no caller-side loop drives the program, so every step
  -- runs on a carrier and the completion is awaited by a bounded round count rather than by a park. Clause one
  -- reads the parallel entry itself, not this.
  let fanOutPush (e : Runtime.Executor 256) (workers : Nat) (cell : LeanIn.Task.Join Unit)
      (prog : LeanIn.Task.Async Unit) : IO Unit := do
    let c ← Runtime.startCarriers e workers
    let _ ← Runtime.Handle.spawn (Runtime.handle e) Runtime.Priority.normal prog
    let _ ← awaitRounds cell
    c.stop
    c.join

  -- ============ clause one: the work is spread over the carriers ============
  -- The one shape is the multi-carrier entry, `Runtime.runCarriers e p program`: it starts the `p` carriers
  -- and submits the program's root to the shared inject, and the mode's own thread — which is **not** a
  -- carrier — waits on the program's cell. The detector compares the tids that ran with the carriers' own
  -- recorded tids, and the affirmative control is the same program at `P = 1`, which reads a single carrier.
  let parallelArm (workers : Nat) : IO (Nat × List UInt64 × List UInt64 × Nat) := do
    let e ← Runtime.Executor.newMetered 256 workers
    let h := Runtime.handle e
    -- the tid log and the completion count are written by items that run on the carriers, so both are
    -- `Std.Mutex`-guarded rather than a cell several threads would read and write unguarded
    let ran ← Std.Mutex.new ([] : List UInt64)
    let done ← Std.Mutex.new (0 : Nat)
    let all ← LeanIn.Task.Join.new (α := Unit)
    let fin ← LeanIn.Task.Join.new (α := Unit)
    let body : LeanIn.Task.Async Unit := LeanIn.Task.Async.ofIO do
      ran.atomically do set ((← get) ++ [← IO.getTID])
      let k ← done.atomically do let k ← get; set (k + 1); return k
      if k + 1 == n then
        -- The body's step runs on a carrier it cannot name, and the waiter it wakes is parked: the shared
        -- route is the one any thread may take, and its push unparks under the shared cell's own lock.
        LeanIn.Task.Join.resolve all (Runtime.sharedPush e) ()
      else pure ()
    let root : LeanIn.Task.Async Unit := do
      LeanIn.Task.Async.ofIO do
        for _ in List.range n do
          let _ ← Runtime.Handle.spawn h Runtime.Priority.normal body
      let token ← LeanIn.Task.Async.ofIO LeanIn.Task.Cancel.new
      LeanIn.Task.Async.await ⟨all, token⟩
      let push ← LeanIn.Task.Async.push
      LeanIn.Task.Async.ofIO (LeanIn.Task.Join.resolve fin push ())
    let (c, _) ← Runtime.runCarriers e workers root
    -- how many carriers the entry actually started: `Carriers.count` reads the thread array, so it is `0`
    -- under the staged entry (no carriers) and `workers` under the fixed one. Read before `stop`/`join`,
    -- which do not change the array.
    let started := c.count
    c.stop
    c.join
    -- the carriers recorded their own tids as they started, and the runtime's own counters say what they fired
    let counters := (← e.metrics).getD []
    let tids := counters.filterMap (fun cc => if cc.tid == 0 then none else some cc.tid)
    let marked := (counters.map (fun cc => cc.fired)).sum
    return (started, tids, ← ran.atomically do return (← get), marked)
  let (carriersStarted, carrierTids, ranTids, marked) ← parallelArm p
  stage "clause one, P carriers"
  let distinctCarriers := (distinctOf ranTids).length
  let (_, _, ranTids1, _) ← parallelArm 1
  stage "clause one, P = 1 control"
  let carrierCount1 := (distinctOf ranTids1).length

  -- ============ clause three: a push from this thread wakes a parked carrier ============
  let e3 ← Runtime.Executor.newMetered 256 p
  let h3 := Runtime.handle e3
  let hooks3 ← Runtime.Hooks.new
  let c3 ← Runtime.startCarriers e3 p
  stage "clause three, carriers started"
  let ran1Tids ← Std.Mutex.new ([] : List UInt64)
  let ran2Tids ← Std.Mutex.new ([] : List UInt64)
  -- every carrier parked and nothing ready: the state a push is the waking event for
  let mut parkedBefore := 0
  let mut readyBefore := 0
  let mut parkedRounds := 0
  while (parkedBefore ≠ p || readyBefore ≠ 0) && parkedRounds < bound do
    let m ← Runtime.Handle.metrics h3
    parkedBefore := m.parked
    readyBefore := m.ready
    parkedRounds := parkedRounds + 1
  let first ← LeanIn.Task.Join.new (α := Unit)
  let _ ← Runtime.Handle.spawn h3 Runtime.Priority.normal (LeanIn.Task.Async.ofIO do
    ran1Tids.atomically do set ((← get) ++ [← IO.getTID])
    LeanIn.Task.Join.resolve first (Runtime.sharedPush e3) ())
  let (_, wokeRounds) ← awaitRounds first
  let second ← LeanIn.Task.Join.new (α := Unit)
  let _ ← Runtime.Handle.spawn h3 Runtime.Priority.normal (LeanIn.Task.Async.ofIO do
    ran2Tids.atomically do set ((← get) ++ [← IO.getTID])
    LeanIn.Task.Join.resolve second (Runtime.sharedPush e3) ())
  let _ ← awaitRounds second
  let m3 ← Runtime.Handle.metrics h3
  let parkedAfter := m3.parked
  let readyAfter := m3.ready
  c3.stop
  c3.join
  stage "clause three, drained"
  -- the carriers' own tids, read after the join: a carrier records its id before it enters the loop, and the
  -- read is after the threads have exited, so what the pushed work ran on is compared against a complete set
  let carrierTids3 ← c3.tids
  let (inFlightAfter, _) ← e3.observe
  let pendingHooks ← Runtime.pending hooks3
  let ranTidList ← ran1Tids.atomically do return (← get)
  let ran2List ← ran2Tids.atomically do return (← get)
  let ran3 := ranTidList ++ ran2List
  let ranTid := match ran3 with
    | t :: _ => toString t
    | []     => "-"
  let inWorkerTids :=
    if !ran3.isEmpty && ran3.all (fun t => carrierTids3.contains t) then "yes" else "no"

  -- ============ the scale arm: the same wake at n = 100000 ============
  let eS ← Runtime.Executor.newMetered 256 p
  let hS := Runtime.handle eS
  let cS ← Runtime.startCarriers eS p
  stage "scale arm, carriers started"
  let doneS ← Std.Mutex.new (0 : Nat)
  let allS ← LeanIn.Task.Join.new (α := Unit)
  let bodyS : LeanIn.Task.Async Unit := LeanIn.Task.Async.ofIO do
    let k ← doneS.atomically do let k ← get; set (k + 1); return k
    if k + 1 == scaleN then
      LeanIn.Task.Join.resolve allS (Runtime.sharedPush eS) ()
    else pure ()
  for _ in List.range scaleN do
    let _ ← Runtime.Handle.spawn hS Runtime.Priority.normal bodyS
  stage "scale arm, pushed"
  let _ ← awaitRounds allS
  stage "scale arm, polled"
  cS.stop
  cS.join
  stage "scale arm, drained"
  let (remaining, _) ← eS.observe

  -- ============ clause two: one thief takes from the ring, never from the slot ============
  let e2 ← Sched.Executor.new Nat 256 (max 3 p)
  -- the ring victim: worker 0's ring holds 200 and its slot is empty, so a thief that keeps part of what it
  -- took is visible as a ring that lost more than the `stolen` it counted
  for x in List.range 200 do e2.submit x
  let ringOf (st : Sched.Snapshot Nat 256) (i : Nat) : Nat :=
    match st.workers[i]? with
    | some w => w.ring.size
    | none   => 0
  let slotOf (st : Sched.Snapshot Nat 256) (i : Nat) : Option Nat :=
    match st.workers[i]? with
    | some w => w.lifo
    | none   => none
  let thiefTid ← IO.getTID
  let victimRingBefore := ringOf (← e2.snapshot) 0
  let victimSlotBefore := slotOf (← e2.snapshot) 0
  let stolen ← e2.stealInto 1 0
  let victimRingAfter := ringOf (← e2.snapshot) 0
  let victimSlotAfter := slotOf (← e2.snapshot) 0
  -- the thief's own pool, read after the steal: the batch cut stages the second element in the thief's slot,
  -- where the design leaves it unchanged
  let thiefRingAfter := ringOf (← e2.snapshot) 1
  let thiefSlotAfter := slotOf (← e2.snapshot) 1
  let emptyVictimRingBefore := ringOf (← e2.snapshot) 1
  let stolenFromEmpty ← e2.stealInto 0 1
  -- the slot-only victim: worker 2 holds one in its slot and nothing in its ring, so the same call that
  -- reads `some` on the ring victim reads `none` here — the LIFO slot is out of a thief's reach. Its slot is
  -- read before *and* after the call and `slotStolen` is computed from the two occupancy readings, not from
  -- the call's return: under a ring-only steal an empty slot reads `none` too, so a `no` derived from the
  -- return would pass vacuously. It reads `no` exactly when the slot was occupied and is still occupied after.
  e2.spawnInto 2 900
  let slotVictimSlotBefore := slotOf (← e2.snapshot) 2
  let _ ← e2.stealInto 0 2
  let slotVictimSlotAfter := slotOf (← e2.snapshot) 2
  let slotStolen := slotVictimSlotBefore.isSome && slotVictimSlotAfter.isSome
  stage "clause two, steal read"

  -- ============ the rows: the measurement conditions, printed and never asserted ============
  let batchN := 500
  let iterations := 500
  let leaninSum ← Std.Mutex.new (0 : Nat)
  let nativeSum ← Std.Mutex.new (0 : Nat)
  let bodyJob (sink : Std.Mutex Nat) (k : Nat) : IO Unit := do
    let mut acc := k
    for i in List.range iterations do acc := (acc * 31 + i) % 1000003
    sink.atomically do set ((← get) + acc)
  -- ours: the batch on `wp` carriers, through the same capability clause one uses
  let leaninBatch (wp : Nat) : IO Nat := do
    let e ← Sched.Executor.new LeanIn.Task.Item 256 wp
    let h := Runtime.handle e
    let done ← Std.Mutex.new (0 : Nat)
    let all ← LeanIn.Task.Join.new (α := Unit)
    let fin ← LeanIn.Task.Join.new (α := Unit)
    let body : LeanIn.Task.Async Unit := LeanIn.Task.Async.ofIO do
      bodyJob leaninSum (← done.atomically do return (← get))
      let k ← done.atomically do let k ← get; set (k + 1); return k
      if k + 1 == batchN then
        LeanIn.Task.Join.resolve all (Runtime.sharedPush e) ()
      else pure ()
    let root : LeanIn.Task.Async Unit := do
      LeanIn.Task.Async.ofIO do
        for _ in List.range batchN do
          let _ ← Runtime.Handle.spawn h Runtime.Priority.normal body
      let token ← LeanIn.Task.Async.ofIO LeanIn.Task.Cancel.new
      LeanIn.Task.Async.await ⟨all, token⟩
      let push ← LeanIn.Task.Async.push
      LeanIn.Task.Async.ofIO (LeanIn.Task.Join.resolve fin push ())
    let t0 ← IO.monoNanosNow
    fanOutPush e wp fin root
    let t1 ← IO.monoNanosNow
    return t1 - t0
  -- the native pool: the same bodies on `Std.Async`'s own workers, whose width is this reading
  let nativeBatch : IO (Nat × Nat) := do
    let tids ← Std.Mutex.new ([] : List UInt64)
    let t0 ← IO.monoNanosNow
    Std.Async.Async.block do
      let hs ← (List.range batchN).mapM (fun k => Std.Async.async (do
        tids.atomically do set ((← get) ++ [← IO.getTID])
        bodyJob nativeSum k))
      for h in hs do let _ ← Std.Async.await h
      pure ()
    let t1 ← IO.monoNanosNow
    return (t1 - t0, (distinctOf (← tids.atomically do return (← get))).length)
  -- the batch shape, swept over `p = 1, 2, 4, 8`, ours beside the native pool's own figure in this
  -- invocation, arm-by-arm, each arm's minimum over the rounds
  let mut nativeThreads := 0
  let mut ratioP1 := 0
  let mut ratioPMax := 0
  let cores ← boxCores
  -- Our arms are capped at the box's core count, and the native pool's width is a fixed configuration taken
  -- once for the whole sweep: the two arms are therefore different widths by construction, so `ratio` reads
  -- ours-at-`p` against a fixed native pool rather than a same-width scaling, and both widths and the core
  -- count are on the rows. An arm whose `p` would exceed the core count is dropped rather than oversubscribed.
  let sweep := [1, 2, 4, 8].filter (fun wp => wp ≤ max 1 cores)
  let pMax := sweep.reverse.head?.getD 1
  for wp in sweep do
    stage s!"batch arm p = {wp}"
    let mut leaninNs := 0
    let mut nativeNs := 0
    for _ in List.range 3 do
      let l ← leaninBatch wp
      let (nv, nt) ← nativeBatch
      if leaninNs == 0 || l < leaninNs then leaninNs := l
      if nativeNs == 0 || nv < nativeNs then nativeNs := nv
      if nt > nativeThreads then nativeThreads := nt
    let ratio := if nativeNs == 0 then 0 else leaninNs * 100 / nativeNs
    if wp == 1 then ratioP1 := ratio
    if wp == pMax then ratioPMax := ratio
    IO.println s!"parbatch|p={wp}|n={batchN}|leaninUs={leaninNs / 1000}|nativeUs={nativeNs / 1000}|ratio={ratio}|nativeThreads={nativeThreads}|cores={cores}"
  -- The condition is stated to its endpoints and nowhere else: `ratio(pMax)` against `ratio(1)`, with a
  -- halving as the stated margin. The interior arms are printed and expressly not asserted between their
  -- neighbours, because four points at the recorded spread cannot resolve pointwise monotonicity.
  IO.println s!"parbatchcond|pMin=1|pMax={pMax}|ratioMin={ratioP1}|ratioMax={ratioPMax}|margin=half|met={if ratioPMax * 2 <= ratioP1 then "yes" else "no"}|nativeWidth={nativeThreads} (fixed across p)|ourArms=capped at min(8, cores={cores})|interior=reported, not asserted"
  IO.println s!"  SC18 batch checksum (printed, so neither arm's work can be elided): leanin={← leaninSum.atomically do return (← get)} native={← nativeSum.atomically do return (← get)}"

  -- the chain: a dependent chain beside a native `Task` chain, in this invocation. Each link spawns and
  -- awaits the next, so the links are sequential and — the structural half — follow the carrier that ran
  -- their parent. The staged parallel entry drives the program on the calling thread, so the chain runs on
  -- one thread and the links' own `Async.spawn`/`await` pushes (owner-made) never leave it; a link-per-leaf
  -- chain may migrate, and that is not the shape this row measures. The two arms below are the same
  -- construction with and without the arm's own per-link tid record, and only the un-instrumented arm is
  -- the recorded shape the 7.6× claim is about: a `tids.modify (· ++ …)` on each of two thousand links is
  -- quadratic and would be measured as the chain.
  let links := 2000
  let chainCarriers ← IO.mkRef 0
  let chainOurs (instrumented : Bool) : IO (Nat × Nat) := do
    let e ← Runtime.Executor.newMetered 256 p
    let tids ← IO.mkRef ([] : List UInt64)
    let fin ← LeanIn.Task.Join.new (α := Unit)
    let rec go (k : Nat) : LeanIn.Task.Async Unit := do
      if k = 0 then pure ()
      else
        let h ← LeanIn.Task.Async.spawn (LeanIn.Task.Async.ofIO do
          if instrumented then tids.modify (· ++ [← IO.getTID]) else pure ())
        let _ ← LeanIn.Task.Async.await h
        go (k - 1)
    let prog : LeanIn.Task.Async Unit := do
      go links
      let push ← LeanIn.Task.Async.push
      LeanIn.Task.Async.ofIO (LeanIn.Task.Join.resolve fin push ())
    -- The carriers are started, so the *construction* is an **affirmative** control rather than a
    -- construction artifact: with `p` carriers running, a thief can reach a ring item of the carrier running
    -- the chain, so a crossing is possible, and `chainCarriers` is a reading of which carrier fired each link
    -- rather than a fixed assertion. The chain's links live in the LIFO
    -- slot, which a ring-only steal cannot see. The program is
    -- pushed through the off-carrier capability and its cell is polled by a bounded round count, so the
    -- caller never drives worker 0 alongside the worker-0 carrier — the extra driver is what the staged wait
    -- accounting cannot survive at P carriers (a bounded poll cannot hang on it).
    let c ← Runtime.startCarriers e p
    let _ ← Runtime.Handle.spawn (Runtime.handle e) Runtime.Priority.normal prog
    let t0 ← IO.monoNanosNow
    let _ ← awaitRounds fin
    let t1 ← IO.monoNanosNow
    c.stop
    c.join
    return ((t1 - t0) / links, (distinctOf (← tids.get)).length)
  -- the native counterpart of the same dependent chain: one pool task spawned and joined per link, each link
  -- beginning only after the previous one completed. Spawning the next task *inside* the previous one would
  -- nest one blocked wait per link and drain the pool's threads, which is a property of the fixture rather than
  -- of the pool; the loop keeps one task in flight and is the shape the recorded native figure was taken with.
  let nativeChain : IO Nat := do
    let rec nativeGo (k : Nat) : IO Unit := do
      if k = 0 then pure ()
      else
        let t ← IO.asTask (pure ()) _root_.Task.Priority.default
        match ← IO.wait t with
        | .ok _    => pure ()
        | .error _ => pure ()
        nativeGo (k - 1)
    let t0 ← IO.monoNanosNow
    nativeGo links
    let t1 ← IO.monoNanosNow
    return (t1 - t0) / links
  let mut chainInstrNs := 0
  let mut chainPlainNs := 0
  let mut chainNativeNs := 0
  stage "chain arm start"
  for _ in List.range 3 do
    let (li, dc) ← chainOurs true
    let (lp, _) ← chainOurs false
    let nv ← nativeChain
    if chainInstrNs == 0 || li < chainInstrNs then chainInstrNs := li
    if chainPlainNs == 0 || lp < chainPlainNs then chainPlainNs := lp
    if chainNativeNs == 0 || nv < chainNativeNs then chainNativeNs := nv
    chainCarriers.set dc
  stage "chain arm done"
  -- `ratio` is a multiplier — the native per-link figure over ours — and each row names the construction it
  -- priced, because only the un-instrumented arm is comparable to the recorded chain claim.
  let mult (num den : Nat) : String :=
    if den == 0 then "-"
    else
      let h := num * 100 / den
      let frac := h % 100
      s!"{h / 100}.{if frac < 10 then "0" else ""}{frac}"
  IO.println s!"chain|construction=Async.spawn/await, per-link tid record|links={links}|leaninNs={chainInstrNs}|nativeNs={chainNativeNs}|ratio={mult chainNativeNs chainInstrNs}|chainCarriers={← chainCarriers.get}"
  IO.println s!"chain|construction=Async.spawn/await, no per-link instrumentation (recorded shape)|links={links}|leaninNs={chainPlainNs}|nativeNs={chainNativeNs}|ratio={mult chainNativeNs chainPlainNs}|chainCarriers=n/a"

  -- the driven steal against a local take: the victim's ring is refilled outside the window, then the calls
  -- are timed, so the figure is one call's cost rather than a refill's
  let sbFill := 255
  let sbRounds := 3
  stage "steal bench start"
  let eB ← Sched.Executor.new Nat 256 2
  let refill : IO Unit := do
    for x in List.range sbFill do eB.submit x
  let mut stealNs := 0
  let mut takeNs := 0
  for _ in List.range sbRounds do
    refill
    let s0 ← IO.monoNanosNow
    for _ in List.range sbFill do let _ ← eB.stealInto 1 0
    let s1 ← IO.monoNanosNow
    refill
    let t0 ← IO.monoNanosNow
    for _ in List.range sbFill do let _ ← eB.takeFor 0
    let t1 ← IO.monoNanosNow
    if stealNs == 0 || s1 - s0 < stealNs then stealNs := s1 - s0
    if takeNs == 0 || t1 - t0 < takeNs then takeNs := t1 - t0
  -- the distinct victims a round of those calls names: the driven steal names victim 0, and each local take
  -- names the victim the worker's own round-robin picks for it
  let victimsScanned := ([0, (0 + 1) % 2].eraseDups).length
  IO.println s!"stealbench|n={sbFill * sbRounds}|stealNs={stealNs / sbFill}|localTakeNs={takeNs / sbFill}|victimsScanned={victimsScanned}"

  -- ============ the records, after the rows ============
  let runNow ← IO.monoNanosNow
  let runUs := (runNow - runStart) / 1000
  -- The mode's own configuration, as an unasserted line: the wake detector compares `wokeRounds` against this
  -- bound rather than a literal, so a mode run at another bound cannot silently pass.
  IO.println s!"carrierscfg|bound={bound}|workers={p}"
  IO.println (s!"carriers|carriers={carriersStarted}|p={p}|carrierTids={tidsText carrierTids}|ranTids={tidsText ranTids}"
    ++ s!"|distinctCarriers={distinctCarriers}|carrierCount1={carrierCount1}|chainCarriers={← chainCarriers.get}"
    ++ s!"|parkedBefore={parkedBefore}|readyBefore={readyBefore}|ranTid={ranTid}|spawnTid={spawnTid}"
    ++ s!"|inWorkerTids={inWorkerTids}|wokeRounds={wokeRounds}|ran1={if ranTidList.isEmpty then "no" else "yes"}"
    ++ s!"|ran2={if ran2List.isEmpty then "no" else "yes"}|parkedAfter={parkedAfter}|readyAfter={readyAfter}"
    ++ s!"|inFlightAfter={inFlightAfter}|pendingHooks={pendingHooks}|scaleN={scaleN}|remaining={remaining}"
    ++ s!"|runUs={runUs}")
  IO.println (s!"steal|victimRingBefore={victimRingBefore}|victimSlotBefore={slotText victimSlotBefore}"
    ++ s!"|stolen={match stolen with | some _ => 1 | none => 0}|victimRingAfter={victimRingAfter}"
    ++ s!"|victimSlotAfter={slotText victimSlotAfter}"
    ++ s!"|stolenFromEmpty={match stolenFromEmpty with | some _ => 1 | none => 0}"
    ++ s!"|emptyVictimRingBefore={emptyVictimRingBefore}"
    ++ s!"|slotStolen={if slotStolen then "no" else "yes"}"
    ++ s!"|slotVictimSlotBefore={slotText slotVictimSlotBefore}"
    ++ s!"|thiefRingAfter={thiefRingAfter}|thiefSlotAfter={slotText thiefSlotAfter}"
    ++ s!"|thiefTid={thiefTid}|victimTid={thiefTid}")
  IO.println s!"sendctl|marked={marked}|unmarkedPushes=0"
  IO.println carriersCtlLine
  -- The two lines above are **descriptions, not evidence**: `sendctl|unmarkedPushes` prints the constant `0`
  -- the marked path makes true and `carriersctl|` states what the fixture is expected to exercise, both built
  -- so that they pass by construction. The authority for the near-miss rejections is the shell fixture's own
  -- exercises, not these lines, so nothing takes a printed constant here for a reading of the system.
  IO.eprintln "SC18 note: sendctl| and carriersctl| above are descriptions of the fixture's exercises, not readings of the system"
  stage "records printed"
  (← IO.getStdout).flush
  return 0

/-- Run `m` under the request scope and report how it ended. The machine's effects are its own leaves, so this
touches no socket, clock or external service. -/
def settleOutcome (m : LeanIn.Runtime.VM α) : IO (LeanIn.Runtime.Outcome α) := do
  let cell ← IO.mkRef (none : Option (LeanIn.Runtime.Outcome α))
  LeanIn.Runtime.VM.runAsync (LeanIn.Runtime.VM.requestScope m) (fun o => cell.set (some o))
  match ← cell.get with
  | some o => return o
  | none => throw (IO.userError "vm abort control: the scoped machine never resolved its raw cell")

/-- An outcome's tag and reason, for a control's assertion to name what it saw. -/
def outcomeText {α : Type} : LeanIn.Runtime.Outcome α → String
  | .ok _ => "ok"
  | .error e => "error " ++ toString e
  | .aborted r => "aborted " ++ toString r

/-- **The VM abort controls.** An abort is not a raise: it passes `tryE` and `attempt` wherever it happens, only
`tryAbort` handles it, and the transport wrapper classifies only the operation it wraps — a client's later
`throwE` stays ordinary. These fail this executable if any clause does not hold.

The last clause is the response writer's relation (`C3`): the writer's own transport wrapper, applied to a
scripted leaf in place of a socket send, must reach the request scope as an abort with the middleware's 500 path
never running — while the same detector, given an ordinary `Http:`-prefixed route error, must see that 500. The
fake alone does not prove the production relation; the callsite audit of `Stream.responseWriter` accompanies it. -/
def controlVMAbort : IO Unit := do
  let sentinel := IO.userError "vm abort control: transport sentinel"
  let abortedWant := "aborted " ++ toString sentinel
  let errorWant := "error " ++ toString sentinel
  let expect {α : Type} (label : String) (want : String) (m : LeanIn.Runtime.VM α) : IO Unit := do
    let got := outcomeText (← settleOutcome m)
    unless got == want do
      throw (IO.userError s!"vm abort control: {label}: expected {want}, got {got}")
  -- Where the abort is raised, and what catches it.
  expect "a direct abort under the request scope" abortedWant (LeanIn.Runtime.VM.abort sentinel : LeanIn.Runtime.VM Unit)
  expect "an abort behind VM.attempt" abortedWant
    (LeanIn.Runtime.VM.attempt (LeanIn.Runtime.VM.abort sentinel : LeanIn.Runtime.VM Unit))
  expect "an abort behind tryE" abortedWant
    (LeanIn.Runtime.VM.tryE (LeanIn.Runtime.VM.abort sentinel : LeanIn.Runtime.VM Unit) fun _ => return ())
  -- The transport wrapper: its own failure aborts, and the classification stops at the operation.
  expect "a transport failure under the request scope" abortedWant
    (LeanIn.Runtime.VM.abortOnFailure (fun (_ : Unit → IO Unit) (fail : IO.Error → IO Unit) => fail sentinel))
  expect "a transport failure behind VM.attempt" abortedWant
    (LeanIn.Runtime.VM.attempt (LeanIn.Runtime.VM.abortOnFailure (fun (_ : Unit → IO Unit) (fail : IO.Error → IO Unit) => fail sentinel)))
  expect "an ordinary throw after a successful wrapped leaf" errorWant
    (do discard (LeanIn.Runtime.VM.abortOnFailure fun kok _ => kok ())
        throw sentinel : LeanIn.Runtime.VM Unit)
  expect "an abort after a successful wrapped leaf" abortedWant
    (do discard (LeanIn.Runtime.VM.abortOnFailure fun kok _ => kok ())
        LeanIn.Runtime.VM.abort sentinel : LeanIn.Runtime.VM Unit)
  -- The lifted leaf: its own failure is ordinary, and it carries the abort channel for what follows.
  expect "a lifted IO failure" errorWant
    (monadLift (throw sentinel : IO Unit) : LeanIn.Runtime.VM Unit)
  -- An unscoped abort has no value to resolve, so the runner fails loudly rather than closing quietly.
  let uncaught (label : String) (act : IO Unit) : IO Unit := do
    let caught ← IO.mkRef (none : Option String)
    try act catch e => caught.set (some (toString e))
    match ← caught.get with
    | none => throw (IO.userError s!"vm abort control: {label}: the abort was swallowed")
    | some m =>
      unless m == toString sentinel do
        throw (IO.userError s!"vm abort control: {label}: raised {m}, expected {toString sentinel}")
  uncaught "VM.run" (LeanIn.Runtime.VM.run (LeanIn.Runtime.VM.abort sentinel : LeanIn.Runtime.VM Unit))
  let cell : LeanIn.Runtime.RawCell Unit ← LeanIn.Runtime.RawCell.new
  uncaught "VM.runToCell" (LeanIn.Runtime.VM.runToCell (LeanIn.Runtime.VM.abort sentinel : LeanIn.Runtime.VM Unit) cell)
  -- A scoped machine completes both runners: the scope consumes the abort, so nothing reaches the top-level throw
  -- and the raw cell is resolved with the tagged outcome.
  let runFailure ← IO.mkRef (none : Option String)
  try
    LeanIn.Runtime.VM.run (do
      discard (LeanIn.Runtime.VM.requestScope (LeanIn.Runtime.VM.abort sentinel : LeanIn.Runtime.VM Unit))
      pure ())
  catch e => runFailure.set (some (toString e))
  match ← runFailure.get with
  | none => pure ()
  | some m => throw (IO.userError s!"vm abort control: a scoped VM.run raised {m}")
  let cellOutcome ← IO.mkRef (none : Option String)
  let scopedCell : LeanIn.Runtime.RawCell (LeanIn.Runtime.Outcome Unit) ← LeanIn.Runtime.RawCell.new
  LeanIn.Runtime.VM.runToCell
    (LeanIn.Runtime.VM.requestScope (LeanIn.Runtime.VM.abort sentinel : LeanIn.Runtime.VM Unit)) scopedCell
  LeanIn.Runtime.RawCell.await scopedCell (fun o => cellOutcome.set (some (outcomeText o)))
  match ← cellOutcome.get with
  | none => throw (IO.userError "vm abort control: a scoped VM.runToCell left its cell unresolved")
  | some got =>
    unless got == abortedWant do
      throw (IO.userError s!"vm abort control: a scoped VM.runToCell resolved {got}, expected {abortedWant}")
  -- ==== C3: the streaming response writer's transport classification ====
  let head ← (match LeanIn.Http.H1.parseHead
      "GET /probe HTTP/1.1\r\nHost: x\r\n\r\n".toUTF8 0 {} with
    | .ok h _ => pure h
    | _ => throw (IO.userError "vm abort control: could not parse the probe request head"))
  let fiveHundreds ← IO.mkRef (0 : Nat)
  let detectStart : LeanIn.Http.H1.ResponseHead → LeanIn.Runtime.VM Unit :=
    fun rh => do
      if rh.status == 500 then
        (monadLift (do
          let n : Nat ← (fiveHundreds.get : IO Nat)
          (fiveHundreds.set (n + 1) : IO Unit)) : LeanIn.Runtime.VM Unit)
      else pure ()
  -- The writer whose `write` is the writer's own wrapper around a scripted completion: no socket, one sentinel.
  let failingWriter : LeanIn.Http.Server.ResponseWriter :=
    { sendContinue := pure ()
      interim := fun _ => pure ()
      start := detectStart
      write := fun _ => LeanIn.Runtime.VM.abortOnFailure fun _ fail => fail sentinel
      finish := pure ()
      status := pure (true, true, false)
      code := pure (some 500) }
  let okWriter : LeanIn.Http.Server.ResponseWriter :=
    { sendContinue := pure ()
      interim := fun _ => pure ()
      start := detectStart
      write := fun _ => pure ()
      finish := pure ()
      status := pure (true, true, false)
      code := pure (some 500) }
  let emptyReader : LeanIn.Http.Server.BodyReader :=
    { recv := fun _ => pure none, drained := pure true, leftover := pure .empty }
  let catchErrorsStream (h : LeanIn.Http.Server.StreamHandler) :
      LeanIn.Http.Server.StreamHandler := fun _ _ w => do
    match ← LeanIn.Runtime.VM.attempt (h head emptyReader w) with
    | .ok _ => pure ()
    | .error e =>
      LeanIn.Http.Server.Stream.respond w
        { status := 500, reason := "Internal Server Error" } (toString e).toUTF8
  let tripWireRoute : LeanIn.Http.Server.StreamHandler := fun _ _ w => do
    w.write "body".toUTF8
    throw (IO.userError "vm abort control tripwire: a step after the failed write ran")
  let aborted := outcomeText (← settleOutcome
    (catchErrorsStream tripWireRoute head emptyReader failingWriter))
  unless aborted == abortedWant do
    throw (IO.userError s!"vm abort control: a failed response write: expected {abortedWant}, got {aborted}")
  unless (← fiveHundreds.get) == 0 do
    throw (IO.userError "vm abort control: the middleware answered a transport failure with a 500")
  -- The driver's fallback response — a handler that answers nothing — is sent inside the request scope. The
  -- affirmative clause: with a normal writer the fallback is the 500 the detector sees. The load-bearing clause:
  -- with a writer whose head send fails the transport's way, that failure is an abort at the scope (what lets the
  -- driver close and report it), not a raise that escapes to the runner.
  let fallbackWriter (failStart : Bool) : LeanIn.Http.Server.ResponseWriter :=
    { sendContinue := pure ()
      interim := fun _ => pure ()
      start := fun rh =>
        if failStart then
          (LeanIn.Runtime.VM.abortOnFailure
            (fun (_ : Unit → IO Unit) (f : IO.Error → IO Unit) => f sentinel) : LeanIn.Runtime.VM Unit)
        else detectStart rh
      write := fun _ => pure ()
      finish := pure ()
      status := pure (true, true, false)
      code := pure (some 500) }
  fiveHundreds.set 0
  let fallbackOk := outcomeText (← settleOutcome
    (LeanIn.Http.Server.Stream.respond (fallbackWriter false)
      { status := 500, reason := "Internal Server Error" } "".toUTF8))
  unless fallbackOk == "ok" do
    throw (IO.userError s!"vm abort control: the driver's fallback response: expected ok, got {fallbackOk}")
  unless (← fiveHundreds.get) == 1 do
    throw (IO.userError s!"vm abort control: the fallback response's 500 was counted {← fiveHundreds.get} times, expected 1")
  let fallbackAbort := outcomeText (← settleOutcome
    (LeanIn.Http.Server.Stream.respond (fallbackWriter true)
      { status := 500, reason := "Internal Server Error" } "".toUTF8))
  unless fallbackAbort == abortedWant do
    throw (IO.userError s!"vm abort control: a failed fallback head send: expected {abortedWant}, got {fallbackAbort}")
  -- The detector's affirmative control: an ordinary, `Http:`-prefixed route error does reach that 500.
  fiveHundreds.set 0
  let ordinaryRoute : LeanIn.Http.Server.StreamHandler :=
    fun _ _ _ => throw (IO.userError "Http: vm abort control ordinary sentinel")
  let ordinary := outcomeText (← settleOutcome
    (catchErrorsStream ordinaryRoute head emptyReader okWriter))
  unless ordinary == "ok" do
    throw (IO.userError s!"vm abort control: the ordinary error route: expected ok, got {ordinary}")
  unless (← fiveHundreds.get) == 1 do
    throw (IO.userError s!"vm abort control: the detector counted {← fiveHundreds.get} 500s, expected exactly 1")
  IO.println ("vmabort|abort-bypasses-attempt=yes|abort-bypasses-tryE=yes|transport-aborts=yes"
    ++ "|later-throw-ordinary=yes|unscoped-abort-loud=yes|scoped-runners-complete=yes|fallback-scoped=yes"
    ++ "|writer-transport-aborts=yes|writer-500-detector=1")

/-- Run every control that can be run, or one executor scenario when named. -/
def runMode (args : List String) : IO UInt32 := do
  -- The affirmative baseline header, in every mode, before any observation: a check reads it to tell
  -- "the executable ran" from "the executable did not", which is a setup error rather than a verdict.
  IO.println "controls for the bridge axioms"
  match args with
  | "--executor-single" :: _ => return ← executorSingle
  | "--executor-trace" :: _ => return ← executorTrace
  | "--executor-park" :: _ => return ← executorPark 256
  | "--executor-queue" :: _ => return ← executorQueue
  | "--executor-lifo-turns" :: _ => return ← executorLifoTurns
  | "--executor-route" :: rest => return ← executorRoute (argNat rest "--bound" 200000)
  | "--runtime-threads" :: _ => return ← runtimeThreads
  | "--runtime-bench" :: _ => return ← runtimeBench
  | "--runtime-tail" :: _ => return ← runtimeTail
  | "--runtime-shared" :: _ => return ← runtimeShared
  | "--runtime-sleep" :: _ => return ← runtimeSleep
  | "--runtime-ops" :: _ => return ← runtimeOps
  | "--runtime-async" :: _ => return ← runtimeAsync
  | "--runtime-unit" :: _ => return ← runtimeUnit
  | "--runtime-chan" :: _ => return ← runtimeChan
  | "--runtime-net" :: _ => return ← runtimeNet
  | "--runtime-http" :: _ => return ← runtimeHttp
  | "--runtime-http-service" :: _ => return ← runtimeHttpService
  | "--runtime-machine-time" :: _ => return ← runtimeMachineTime
  | "--runtime-time" :: _ => return ← runtimeTime
  | "--runtime-time-loser" :: _ => return ← runtimeTimeLoser
  | "--runtime-connect" :: _ => return ← runtimeConnect
  | "--runtime-drain" :: _ => return ← runtimeDrain
  | "--runtime-cancel" :: _ => return ← runtimeCancel
  | "--runtime-blocking" :: _ => return ← runtimeBlocking
  | "--runtime-sync" :: _ => return ← runtimeSync
  | "--runtime-service" :: rest =>
    return ← runtimeService (((argValue rest "--bound").bind String.toNat?).getD 2)
  | "--runtime-registry" :: _ => return ← runtimeRegistry
  | "--runtime-carriers" :: rest =>
    return ← runtimeCarriers (argNat rest "--workers" 4) (argNat rest "--bound" 20000)
  | "--runtime-select" :: _ => return ← runtimeSelect
  | "--runtime-handle" :: rest =>
    let readyFile :=
      match argValue rest "--ready-file" with
      | some p => p
      | none   => (argAfter rest "--ready-file").getD ""
    return ← runtimeHandle readyFile
  | "--executor-replay" :: rest =>
    let seed := ((argValue rest "--seed").bind String.toNat?).getD 0
    let script := (argValue rest "--script").getD "main"
    return ← executorReplay seed script
  | _ => pure ()
  IO.println "  A3 (release without ownership) is not tested — see the header."
  IO.println ""
  controlClock 10000
  controlDedicated
  controlWitness
  controlTryLock
  controlNotifyLost 200
  controlPredicateRecheck 200
  controlVMAbort
  controlTimeoutOverlap
  let _ ← controlMutualExclusion 4 500000
  IO.println ""
  IO.println "  done"
  return 0

/-- The parser keeps the method token: an unknown method must not become a known one, and a known method
still classifies as itself. -/
def h1MethodTokenSelfTest : IO Unit := do
  let parse (s : String) : IO LeanIn.Http.H1.Head := do
    match LeanIn.Http.H1.parseHead s.toUTF8 0 {} with
    | .ok h _ => return h
    | _ => throw (IO.userError s!"h1 method token: could not parse {s}")
  let pf ← parse "PROPFIND /x HTTP/1.1\r\nHost: x\r\n\r\n"
  unless pf.method == .other do
    throw (IO.userError "h1 method token: PROPFIND was classified as a known method")
  unless pf.methodTokenString == "PROPFIND" do
    throw (IO.userError s!"h1 method token: PROPFIND token read as {pf.methodTokenString}")
  let g ← parse "GET /x HTTP/1.1\r\n\r\n"
  unless g.method == .get && g.methodTokenString == "GET" do
    throw (IO.userError s!"h1 method token: GET read as {g.method} / {g.methodTokenString}")

/-- **Run the named mode, then stop the I/O loop this process started.**

The stop is the process's own bookkeeping rather than a mode's: a mode that bound a listener leaves a loop thread
parked in the shim's `uv_run`, and the Lean task manager waits for every dedicated task at shutdown, so without
this the process would print its record and then never exit. It is a no-op in a mode that bound no listener. -/
def main (args : List String) : IO UInt32 := do
  if args.contains "--h1-method-token" then
    h1MethodTokenSelfTest
    IO.println "h1 method token: unknown kept as a token, known classified -- ok"
    return 0
  if args.contains "--raw-registry" then
    LeanIn.Runtime.Io.rawRegistrySelfTest
    IO.println "raw registry: register/take/no-double-take/replace/withdraw, live count 0 -- ok"
    return 0
  let code ← runMode args
  Runtime.Io.stop
  return code

end LeanIn.Test

end
