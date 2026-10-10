import Std
import LeanIn.Sched.Basic
import LeanIn.Sched.Executor
import LeanIn.Runtime.Basic
import LeanIn.Runtime.Leaf
import LeanIn.Runtime.Net
import LeanIn.Runtime.Time
import LeanIn.Runtime.Blocking
import LeanIn.Task.Sync
import LeanIn.Task.Registry

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

def executorTrace : IO UInt32 := do
  let e ← Sched.Executor.new Nat 256 1
  let mut pos : Nat := 0
  for o in traceScript do
    match o with
    | .submit t =>
      e.submit t
      let st ← e.snapshot
      IO.println s!"exec|trace|op=submit|pos={pos}|task={t}|out=inflight{st.1.inFlight}"
    | .enqueue t =>
      -- An external delivery: the same transaction as a submit, under the name the oracle uses for it.
      e.submit t
      let st ← e.snapshot
      IO.println s!"exec|trace|op=enqueue|pos={pos}|task={t}|out=inflight{st.1.inFlight}"
    | .take =>
      let got ← e.take
      let st ← e.snapshot
      match got with
      | some x => IO.println s!"exec|trace|op=take|pos={pos}|task={x}|out=taken{st.1.taken}"
      | none   => IO.println s!"exec|trace|op=take|pos={pos}|task=-|out=none"
    | .park =>
      let granted ← e.park
      let st ← e.snapshot
      if granted then IO.println s!"exec|trace|op=park|pos={pos}|task=-|out=parked{st.2.parked}"
      else IO.println s!"exec|trace|op=park|pos={pos}|task=-|out=none"
    pos := pos + 1
  return 0

/-- **SC2 — an injected completion wakes a waiting carrier, and shutdown delivers the staged work once.**

Two event orders, and neither is decided by elapsed time. In the *notification-first* order the producer
submits before any carrier exists, so a carrier started afterwards finds the work rather than parking. In the
*parked-first* order the carrier is started first, the harness waits until the state *says* it is parked, and
only then does the producer act — which is the order a naive protocol hangs on, since a notification with no
waiter is lost.

Then the shutdown half: two identities staged at the public `submit`, shutdown, and a carrier that runs the
loop until `work` reports stopping. `delivered` is what the carrier actually took, so a drain that reported a
zero count while completing nothing could not pass as one that delivered both.

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
  -- The carrier starts *first*, so it parks; `snapshot` can take the lock because a parked carrier has
  -- released it. The producer acts only once the state says the park has happened, which is what makes this
  -- the order a naive protocol hangs on: a notification with no waiter is lost.
  let w2 ← IO.asTask (do
    match ← e2.work with
    | some _ => got2.set true
    | none   => pure ()) _root_.Task.Priority.dedicated
  let parked ← IO.mkRef false
  let mut tries := 0
  while !(← parked.get) && tries < 1000 do
    IO.sleep 1
    let st ← e2.snapshot
    parked.set (st.2.parked = 1)
    tries := tries + 1
  if ← parked.get then record "parked-first=parked"
  e2.submit 7
  record "producer=emitted-after-park"
  match ← IO.wait w2 with
  | .ok _    => if ← got2.get then record "parked-first=completed"
  | .error e => IO.println s!"executor-park: order 2 errored: {e}"

  -- Shutdown: stage two identities, stop, and let a carrier drain until `work` reports stopping.
  let e3 ← Sched.Executor.new Nat cap 1
  let seen ← IO.mkRef ([] : List Nat)
  let carrier ← IO.asTask (do
    let mut go := true
    while go do
      match ← e3.work with
      | some x => seen.modify (· ++ [x])
      | none   => go := false) _root_.Task.Priority.dedicated
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
  IO.println s!"exec|park|before={before}|after={after}|observed={String.intercalate "," (← events.get)}|queued=[{String.intercalate "," (queued.map toString)}]|delivered=[{String.intercalate "," (delivered.map toString)}]|remaining={st.1.inFlight}"
  return 0

/-- The value of a `--key=value` argument, for the modes that take one. -/
def argValue (args : List String) (key : String) : Option String :=
  args.findSome? fun a =>
    if a.startsWith (key ++ "=") then some ((a.drop (key.length + 1)).toString) else none


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
  let workNs ← best do for _ in List.range k do let _ ← e3.tryTake
  -- The steady state the benchmarks run in: enqueue a step and consume it, so the ring never saturates.
  -- The rows above measure a *burst* -- 20 000 items through a 256-slot ring -- which is a different cost.
  let e4 ← Sched.Executor.new LeanIn.Task.Item 256 1
  let steadyNs ← best do for _ in List.range k do
    e4.spawn item
    let _ ← e4.tryTake
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
  IO.println s!"ops: Join.new {joinNs}ns | Executor.spawn {spawnNs}ns | Executor.submit {submitNs}ns | Executor.tryTake {workNs}ns | spawn+take (steady) {steadyNs}ns"
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

The `+ Pool.submit` row also shows the other cliff: `inject` is a list appended to, so a burst that nobody
drains grows it and the append gets more expensive with every item.

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
  let m ← Std.Mutex.new ({ pool := LeanIn.Sched.emptyPool LeanIn.Task.Item 256,
                            sched := LeanIn.Sched.Scheduler.initial 1 } :
                          LeanIn.Sched.State LeanIn.Task.Item 256)
  let plumb ← best do for _ in List.range k do
    m.atomically do let s ← get; set ({ s with sched := s.sched.enqueue })
  let withsub ← best do for _ in List.range k do
    m.atomically do
      let s ← get
      set ({ s with pool := s.pool.submit item, sched := s.sched.enqueue })
  let withspawn ← best do for _ in List.range k do
    m.atomically do
      let s ← get
      set ({ s with pool := s.pool.spawn item, sched := s.sched.enqueue })
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
    Runtime.echoConn hooks c
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
  IO.println s!"exec|runtime|caller={caller}|steps=[{String.intercalate "," ids}]|external={← external.get}|value={v}|remaining={st.1.inFlight}"
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
        trace := trace ++ [s!"op=take|pos={p}|task={x}|out=taken{st.1.taken}"]
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
    ++ s!"|remaining={st.1.inFlight}")
  return 0

/-- **W3's evidence: timers on our carriers.**

`n` sleepers and one late spawn, with the *order* of the events doing the work a clock would otherwise be asked
to do. Every sleeper records that it started before it sleeps and that it woke afterwards, and a task spawned
while all `n` sleeps are pending records that it ran. If the sleeps occupied the carrier rather than parking on
a timer, the first sleeper's wake would land between the first two starts — so "everything before the first
wake is a start" *is* the overlap, read from the recorded order and not from elapsed time. The two timeout
outcomes are deterministic for the same reason: one inner computation never finishes and must time out, the
other finishes immediately and must not. The measured row is printed and never asserted, for the reason the
socket check gives.

Diagnostic: `lake exe controls --runtime-time`. -/
def runtimeTime : IO UInt32 := do
  let n := 16
  let d : Std.Time.Millisecond.Offset := 50
  let hooks ← Runtime.Hooks.new
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
    Runtime.sleep hooks d
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
    let hit ← Runtime.withTimeout hooks 50 (Runtime.never : LeanIn.Task.Async Unit)
    let miss ← Runtime.withTimeout hooks 200 (pure 7)
    return (hit, miss))
  -- The task layer's first-writer-wins law, and the timeout's own loser actually happening. The two writes are
  -- issued in order rather than raced, because which of two racing writers wins is a scheduling fact and this
  -- is a claim about the operation: the first value stays and the second is ignored. The `withTimeout` below
  -- is the integration half — the computation finishes, its 5 ms timer fires during the 40 ms after it, and
  -- the late write changes nothing. A `Join.resolve` in either position would raise out of the driver instead,
  -- so arriving at the print at all is part of the evidence.
  let (firstWins, lateTimerIgnored) ← Runtime.run e (do
    let cell ← LeanIn.Task.Join.new
    LeanIn.Task.Join.resolveFirst cell (some 1)
    LeanIn.Task.Join.resolveFirst cell (some 2)
    let token ← (LeanIn.Task.Cancel.new : IO LeanIn.Task.Cancel)
    let first ← LeanIn.Task.Async.await (show LeanIn.Task.Task (Option Nat) from ⟨cell, token⟩)
    let late ← Runtime.withTimeout hooks 5 (pure 7)
    Runtime.sleep hooks 40
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
  return 0

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
      monadLift (Runtime.cancel benchHooks h (.error (.userError "bench")) : IO Unit)
      pure ()
    let t2 ← monadLift clock
    let ran ← monadLift (IO.mkRef (0 : Nat) : BaseIO (IO.Ref Nat))
    let parkers ← (List.range benchN).mapM (fun _ =>
      LeanIn.Task.MonadAsync.spawn (do
        monadLift (ran.modify (· + 1) : BaseIO Unit)
        Runtime.awaitPromiseE benchHooks never))
    let _ ← LeanIn.Task.EAsync.ofAsync (Runtime.sleep benchHooks 20)
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
    for _ in List.range benchN do monadLift (LeanIn.Task.Join.resolveFirst cell () : IO Unit)
    let t5 ← monadLift clock
    for _ in List.range benchN do monadLift (Runtime.Hooks.retire benchHooks : IO Unit)
    let t6 ← monadLift clock
    for h in parkers do
      monadLift (Runtime.cancel benchHooks h (.error (.userError "bench")) : IO Unit)
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
    monadLift (Runtime.cancel hooks handle (.error (.userError "canceled")) : IO Unit)
    let afterCancel ← match tok with
      | some tk => ofWork tk
      | none    => pure 0
    pendingAfterRef.set afterCancel
    let ok : Except IO.Error Unit := .ok ()
    monadLift (IO.Promise.resolve ok gate : BaseIO Unit)
    let secondTry ← try
        monadLift (Runtime.cancel hooks handle (.error (.userError "canceled")) : IO Unit)
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
      Runtime.echoConn hooks c) [])) _root_.Task.Priority.dedicated
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
well-formed record and on near misses (`syncctl|`), and a `syncbench|` measurement line that is
printed and never asserted. -/

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

/-- `n` lock/unlock pairs on one mutex, as one computation. -/
def syncLockPairs (m : LeanIn.Task.Sync.Mutex) : Nat → LeanIn.Task.Async Unit
  | 0     => pure ()
  | n + 1 => do
      LeanIn.Task.Sync.Mutex.lock m
      LeanIn.Task.Sync.Mutex.unlock m
      syncLockPairs m n

/-- Yield the rest of this computation as a fresh step on the same carrier, so another computation's step can
run at the boundary. The task layer exposes no primitive for this, so it is spelled here as `ctx.resume` of a
continuation. -/
def syncYield : LeanIn.Task.Async Unit := ⟨fun k ctx => do
  ctx.resume (LeanIn.Task.Item.ofAction (k ()))⟩

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
      LeanIn.Task.Sync.Mutex.unlock m
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
      LeanIn.Task.Sync.Semaphore.release s
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
    for _ in List.range w do
      let _ ← LeanIn.Task.Async.spawn (LeanIn.Task.Sync.Semaphore.acquire s3)
      pure ()
    LeanIn.Task.Sync.Semaphore.release s3)
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
    LeanIn.Task.Sync.Mutex.unlock m
    return 9
  let holderA : LeanIn.Task.Async Nat := do
    LeanIn.Task.Sync.Mutex.lock m
    record "a-enter"
    let hb ← LeanIn.Task.Async.spawn holderB
    let _ ← LeanIn.Task.Async.spawn unrelatedFirst
    let _ ← Runtime.awaitPromiseE hooks aGate
    record "a-exit"
    LeanIn.Task.Sync.Mutex.unlock m
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
      let ok ← LeanIn.Task.Sync.Channel.trySend c (100 + i)
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
      let ok ← LeanIn.Task.Sync.Channel.trySend ctl (300 + i)
      addNat (if ok then ctlAccRef else ctlRejRef) 1

    -- the semaphore's count: two permits, a third refused, one release, one more admitted.
    let sem ← LeanIn.Task.Sync.Semaphore.new 2
    let s1 ← LeanIn.Task.Sync.Semaphore.tryAcquire sem
    let s2 ← LeanIn.Task.Sync.Semaphore.tryAcquire sem
    let s3 ← LeanIn.Task.Sync.Semaphore.tryAcquire sem
    setNat semAccRef ((if s1 then 1 else 0) + (if s2 then 1 else 0))
    setStr semRejRef (if s3 then "yes" else "no")
    LeanIn.Task.Sync.Semaphore.release sem
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
    Runtime.cancel hooks w ()
    LeanIn.Task.Sync.Mutex.unlock m2
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
    Runtime.cancel hooks r ()
    LeanIn.Task.Sync.Channel.send rc 42
    -- The receiver's value is taken by its own stock task once the send resolves its queue entry; that
    -- task runs on the pool, so the probe waits for a stock completion scheduled after the send before
    -- reading the channel. The wait is a completion, not a clock.
    let settle ← IO.asTask (pure (Except.ok () : Except IO.Error Unit)) _root_.Task.Priority.default
    let _ ← Runtime.awaitTask hooks settle
    let gotR ← LeanIn.Task.Sync.Channel.tryRecv rc
    setStr recvRef (match gotR with | some _ => "present" | none => "lost")

    -- (c) a cancelled sender consumes no slot: the sender parks on a full channel, is cancelled,
    -- one value is drained, and a non-parking trySend reads whether a slot is free and whether the
    -- cancelled sender's value has appeared.
    let sc ← LeanIn.Task.Sync.Channel.new Nat 1
    let _ ← LeanIn.Task.Sync.Channel.trySend sc 901
    let sReady ← (IO.Promise.new : IO (IO.Promise (Except IO.Error Unit)))
    let s ← LeanIn.Task.Async.spawn (do
      gateResolve sReady
      LeanIn.Task.Sync.Channel.send sc 999)
    let _ ← Runtime.awaitPromiseE hooks sReady
    Runtime.cancel hooks s ()
    let _ ← LeanIn.Task.Sync.Channel.tryRecv sc
    let sentOk ← LeanIn.Task.Sync.Channel.trySend sc 555
    let held ← LeanIn.Task.Sync.Channel.tryRecv sc
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
          let fired ← LeanIn.Task.EAsync.ofAsync (Runtime.withTimeout hooks timeout
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
    Runtime.serveBounded hooks (← keep.get) bound n body)) _root_.Task.Priority.dedicated
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
      monadLift (Runtime.cancel hooks h3 (.error (.userError "sc15")) : IO Unit)
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

/-- A handle whose cell is already resolved, so a benchmark can await it without a scheduling round. -/
def resolvedTask {α : Type} (v : α) : IO (LeanIn.Task.Task α) := do
  let cell ← LeanIn.Task.Join.new
  LeanIn.Task.Join.resolve cell v
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

/-- Run every control that can be run, or one executor scenario when named. -/
def main (args : List String) : IO UInt32 := do
  -- The affirmative baseline header, in every mode, before any observation: a check reads it to tell
  -- "the executable ran" from "the executable did not", which is a setup error rather than a verdict.
  IO.println "controls for the bridge axioms"
  match args with
  | "--executor-single" :: _ => return ← executorSingle
  | "--executor-trace" :: _ => return ← executorTrace
  | "--executor-park" :: _ => return ← executorPark 256
  | "--executor-queue" :: _ => return ← executorQueue
  | "--runtime-threads" :: _ => return ← runtimeThreads
  | "--runtime-bench" :: _ => return ← runtimeBench
  | "--runtime-tail" :: _ => return ← runtimeTail
  | "--runtime-shared" :: _ => return ← runtimeShared
  | "--runtime-sleep" :: _ => return ← runtimeSleep
  | "--runtime-ops" :: _ => return ← runtimeOps
  | "--runtime-async" :: _ => return ← runtimeAsync
  | "--runtime-unit" :: _ => return ← runtimeUnit
  | "--runtime-net" :: _ => return ← runtimeNet
  | "--runtime-time" :: _ => return ← runtimeTime
  | "--runtime-connect" :: _ => return ← runtimeConnect
  | "--runtime-drain" :: _ => return ← runtimeDrain
  | "--runtime-cancel" :: _ => return ← runtimeCancel
  | "--runtime-blocking" :: _ => return ← runtimeBlocking
  | "--runtime-sync" :: _ => return ← runtimeSync
  | "--runtime-service" :: rest =>
    return ← runtimeService (((argValue rest "--bound").bind String.toNat?).getD 2)
  | "--runtime-registry" :: _ => return ← runtimeRegistry
  | "--runtime-select" :: _ => return ← runtimeSelect
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
  let _ ← controlMutualExclusion 4 500000
  IO.println ""
  IO.println "  done"
  return 0

end LeanIn.Test
