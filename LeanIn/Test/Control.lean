import Std
import LeanIn.Sched.Basic
import LeanIn.Sched.Executor

/-!
# Runtime controls for the bridge axioms

`LeanIn/Theory/Bridge.lean` asserts seven claims about the running `Std` primitives. An axiom nobody
checks is a liability, so each gets a control here — a test that distinguishes "the claim holds" from
"it does not".

Not all seven can be tested, and saying which is part of the point:

* **A1, A2, A5, A7** are controlled below.
* **A3** (release requires ownership) cannot be *tested*, because violating it is undefined behaviour
  — the test would be the defect. It is discharged by reading `mutex.cpp` plus the standard, and the
  model expresses the constraint by having no transition for it.
* **A4** (spurious wakeups) cannot be *forced*: the implementation is permitted to wake spuriously, not
  obliged to. The control is therefore a tolerance test — a `waitUntil`-shaped loop must survive a
  wakeup it did not ask for — rather than an observation of one.
* **A6** is absent from v1 (D2, D11).

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
  let held ← IO.asTask (do return (← Std.BaseMutex.tryLock m)) Task.Priority.dedicated
  let bHeld ← IO.wait held
  let t₁ ← IO.monoNanosNow
  Std.BaseMutex.unlock m
  let free ← IO.asTask (do return (← Std.BaseMutex.tryLock m)) Task.Priority.dedicated
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
    Std.BaseMutex.unlock m) Task.Priority.dedicated
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
        r.set (v + 1)) Task.Priority.dedicated)
  for t in unguarded do let _ ← IO.wait t
  let raw ← r.get

  let m ← Std.Mutex.new (0 : Nat)
  let guarded ← (List.range threads).mapM (fun _ => IO.asTask (do
      for _ in List.range iters do
        m.atomically do set ((← get) + 1)) Task.Priority.dedicated)
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
    Std.BaseMutex.unlock m) Task.Priority.dedicated
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
    return (7 : Nat)) Task.Priority.default
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
      return Task.pure ())
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
    | none   => pure ()) Task.Priority.dedicated
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
    | none   => pure ()) Task.Priority.dedicated
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
      | none   => go := false) Task.Priority.dedicated
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

/-- Run every control that can be run, or one executor scenario when named. -/
def main (args : List String) : IO UInt32 := do
  -- The affirmative baseline header, in every mode, before any observation: a check reads it to tell
  -- "the executable ran" from "the executable did not", which is a setup error rather than a verdict.
  IO.println "controls for the bridge axioms"
  match args with
  | "--executor-single" :: _ => return ← executorSingle
  | "--executor-trace" :: _ => return ← executorTrace
  | "--executor-park" :: _ => return ← executorPark 256
  | _ => pure ()
  IO.println "  A3 (release without ownership) and A6 (thread creation) are not tested — see the header."
  IO.println ""
  controlClock 10000
  controlTryLock
  controlNotifyLost 200
  controlPredicateRecheck 200
  let _ ← controlMutualExclusion 4 500000
  IO.println ""
  IO.println "  done"
  return 0

end LeanIn.Test
