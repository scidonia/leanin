import Std
import LeanIn.Sched.Pool
import LeanIn.Sched.Scheduler

/-!
# The executor's state, and the critical sections around it

`Pool` and `Scheduler` are the two halves of what a worker holds. This file is where they are held
*together*, and that is not a packaging choice: the model's protocol is atomic per transaction — `enqueue`
adds work *and* unparks in one step, `park` checks the work state and parks in one step — and one
`Std.Mutex` around the pair is what makes an executor agree with it.

Three transactions, and the projection that makes them comparable:

| operation | pool | scheduler |
|---|---|---|
| `submit` | `Pool.submit` | `Sched.enqueue` |
| `take` | `Pool.take`, and `Sched.take` only when it returned a task | |
| `park` | unchanged | `Sched.park`, refused while work is held |

`Aligned` -- the scheduler's work count and the pool's held work being one quantity -- is what `take`'s two
halves must not come apart through. **Its preservation is proved**, one theorem per transaction below: a
tick, a submit, a spawn and a take. Those four are the whole of what a transaction can do to the pair — the
two pool operations that add work, the one that removes it, and the allowance refresh that moves neither
side — and the proofs are the pool's own count laws applied to the scheduler's two counters.
`tests/ModelOracle.lean` checks the same equation after every step of its script, which is where it is
observed rather than proved.

`Executor.work` is one step of a worker — take work, or park until there is some — and the carrier loop is
that step run until `none`. The records and the driver that emits them are not here.
-/

namespace LeanIn.Sched

-- `Pool` is built on `Ring`, whose operations need `Inhabited α` (`toList` falls back to `default`), so
-- anything holding a `Pool` needs the instance in scope. Carried once here rather than at each mention.
variable {α : Type} [Inhabited α]

/-- The executor's state: the pool's bookkeeping beside the wake protocol. -/
structure State (α : Type) (cap : Nat) where
  /-- The pool's ring, LIFO slot and inject queue. -/
  pool  : Pool α cap
  /-- The wake protocol, over the workers. -/
  sched : Scheduler
deriving Inhabited, Repr

/-- **One quantity.** The scheduler's work count and the pool's held work are the same number, which is what
lets the two sides of a comparison refer to the same work rather than to two counters that move together by
coincidence. -/
def State.Aligned (st : State α cap) : Prop := st.sched.work = st.pool.inFlight

/-- **The projection onto the model.** The oracle's own `State`, field for field. -/
def State.toModel (st : State α cap) : Model.Pool α × Model.Sched :=
  (st.pool.toModel, st.sched.toModel)

/-- An executor: one mutex over the pair. Every transaction below is one critical section, which is what
makes the model's atomicity a property of this code rather than a hope about the scheduler. -/
structure Executor (α : Type) (cap : Nat) where
  state : Std.Mutex (State α cap)
  /-- A worker waiting for work parks on this. The *state* says a worker is parked; only the condvar makes a
  thread sleep, and a push notifies under the same lock the predicate is re-checked under. -/
  cv    : Std.Condvar
  /-- **What a transaction writes into the cell while it holds the lock.**

`Array.set` copies when its array is still referenced elsewhere, and the cell's own reference to the state
being read is exactly that other reference — so every ring mutation under `Mutex.atomically` was copying the
slots. Writing this value releases the cell's hold, leaving the state the transaction read as the only owner
of its slots, and the mutation then happens in place. Nothing outside the critical section can see it: the
lock is held for the whole transaction, and the value the transaction computes is written back before the
lock is released.

Only sites that *replace* the pool are using it. A site that has to restore the pool it read — a refused
take — cannot, because an in-place mutation would have moved the value it means to restore. -/
  placeholder : State α cap

def Executor.new (α : Type) (cap : Nat) (workers : Nat) : IO (Executor α cap) := do
  -- A placeholder of its own, not the state the cell starts with: a transaction mutates the state it read,
  -- so sharing one value between the cell and the placeholder would let a transaction mutate the placeholder.
  let fresh := { pool := emptyPool α cap, sched := Scheduler.initial workers }
  return { state := ← Std.Mutex.new fresh,
           cv := ← Std.Condvar.new
           placeholder := { pool := emptyPool α cap, sched := Scheduler.initial workers } }

/-- **Submit, without the real-world token.** The body of `submit`, split out because a *waker* runs in
`BaseIO`: a continuation registered on a stock `Task` cannot call an `IO` action, and enqueuing is the one
thing a waker does. Everything here — the state lock, the condvar — is `BaseIO`-compatible, so nothing is
duplicated: `submit` is this plus the token.

The pool takes the work *and* the scheduler records it, as one step; reading `inFlight` afterwards is the work
the pool holds. -/
def Executor.submitBase (e : Executor α cap) (x : α) : BaseIO Unit :=
  e.state.atomically do
    let st ← get
    let wasParked := st.sched.parked ≠ 0
    -- Release the cell's hold before the pool is modified, so the ring's slots are uniquely owned and the
    -- mutation happens in place (see `Placeholder`). The old pool is not read again after this point.
    set e.placeholder
    set ({ st with pool := st.pool.submit x, sched := st.sched.enqueue })
    -- The notify is inside the critical section, which is the discipline the whole protocol rests on: a
    -- worker's predicate is re-checked under this lock, so a wakeup cannot slip between the check and the
    -- wait. `Sched.enqueue` already unparked a worker in the *state*; this is what wakes the thread.
    --
    -- Only when a worker *was* parked, which is what Tokio's `schedule_local` does and what the state
    -- already tells us: with nobody parked there is no thread to wake, and a worker that parks later
    -- re-checks the predicate under this same lock and finds the work, so nothing can be lost by skipping it.
    if wasParked then e.cv.notifyOne

/-- Submit, or an external event delivering work: the one above, in `IO`. -/
def Executor.submit (e : Executor α cap) (x : α) : IO Unit := do e.submitBase x

/-- **Take one item of work, and report the decision.** The pool and the scheduler advance together, or
neither does — a pool that returned a task while the scheduler removed no work would break `Aligned`, and one
lock is what makes that unreachable rather than merely unlikely. A refused scheduler leaves the pool as it
was and reports no item, which is the same refusal the older form returned as `none`. -/
def Executor.takeReport (e : Executor α cap) : IO (Sched.TakeReport α cap) :=
  e.state.atomically do
    let st ← get
    let r := st.pool.takeReport
    match r.item with
    | none => return r
    | some _ =>
      match st.sched.take with
      | none    => return { r with item := none, pool := st.pool }
      | some s' => set ({ st with pool := r.pool, sched := s' }); return r

/-- Take one item of work: the decision without its report. -/
def Executor.take (e : Executor α cap) : IO (Option α) := do
  return (← e.takeReport).item

/-- **A fresh tick: the LIFO allowance refreshes.** Nothing else moves, and the proof is one line because
of it — a tick cannot change what the executor holds, only how it will serve the next take. -/
def Executor.tick (e : Executor α cap) : IO Unit :=
  e.state.atomically do
    let st ← get
    set ({ st with pool := st.pool.tick })

/-- **Local spawn: work that is ready on this worker.** The pool places it in the LIFO slot (displacing the
occupant through the same overflow rule a submit uses), and the scheduler records the work and unparks a
worker, as one step — `Sched.enqueue`, exactly as `submit` does it.

The difference from `submit` is only *where* the pool puts it, which is the whole point of the operation: the
slot is what keeps a chained task on the core that just ran its parent, and it is why the allowance exists. -/
def Executor.spawnBase (e : Executor α cap) (x : α) : BaseIO Unit :=
  e.state.atomically do
    let st ← get
    let wasParked := st.sched.parked ≠ 0
    -- Release the cell's hold before the pool is modified, so the ring's slots are uniquely owned and the
    -- mutation happens in place (see `Placeholder`). The old pool is not read again after this point.
    set e.placeholder
    set ({ st with pool := st.pool.spawn x, sched := st.sched.enqueue })
    if wasParked then e.cv.notifyOne

/-- Local spawn: the one above, in `IO`. -/
def Executor.spawn (e : Executor α cap) (x : α) : IO Unit := do e.spawnBase x

/-- Park: refused while work is held, granted otherwise. The check and the park are one critical section,
which is exactly what the model's `park` encodes and the only reason a wakeup cannot be lost between them:
an `enqueue` must take the same lock to unpark. -/
def Executor.park (e : Executor α cap) : IO Bool :=
  e.state.atomically do
    let st ← get
    match st.sched.park with
    | none    => return false
    | some s' => set ({ st with sched := s' }); return true

/-- Shutdown: the flag is set under the lock, so a park either sees it or is refused. -/
def Executor.stop (e : Executor α cap) : IO Unit :=
  e.state.atomically do
    let st ← get
    set ({ st with sched := st.sched.stop })
    e.cv.notifyAll

omit [Inhabited α] in
/-- A tick moves neither side of the alignment. -/
theorem Aligned.tick (st : State α cap) (h : st.Aligned) : ({ st with pool := st.pool.tick }).Aligned := by
  unfold State.Aligned Pool.inFlight at h ⊢
  unfold Pool.tick at ⊢
  omega

/-- **A submission keeps the alignment.** The pool holds one more and the scheduler records one more, so
the two sides move together — with room or on a full ring, since the eviction is a move. -/
theorem Aligned.submit (st : State α cap) (h : st.Aligned) (x : α) (hw : st.pool.ring.WF)
    (hcap : 0 < cap) :
    ({ st with pool := st.pool.submit x, sched := st.sched.enqueue } : State α cap).Aligned := by
  have hp : (st.pool.submit x).inFlight = st.pool.inFlight + 1 :=
    inFlight_submit st.pool x hw hcap
  unfold State.Aligned at h ⊢
  show (st.sched.enqueue).work = (st.pool.submit x).inFlight
  rw [hp]
  simp only [Scheduler.enqueue]
  omega

/-- **A spawn keeps the alignment.** The slot write and the enqueue are the same pair of moves a submission
makes — the pool holds one more, the scheduler records one more — so the same proof does the work. -/
theorem Aligned.spawn (st : State α cap) (h : st.Aligned) (x : α) (hw : st.pool.ring.WF)
    (hcap : 0 < cap) :
    ({ st with pool := st.pool.spawn x, sched := st.sched.enqueue } : State α cap).Aligned := by
  have hp : (st.pool.spawn x).inFlight = st.pool.inFlight + 1 :=
    spawn_inFlight st.pool x hw hcap
  unfold State.Aligned at h ⊢
  show (st.sched.enqueue).work = (st.pool.spawn x).inFlight
  rw [hp]
  simp only [Scheduler.enqueue]
  omega

/-- **A take keeps the alignment.** The pool holds one fewer and the scheduler's count drops by one, which
is the same move — and this is the transaction `Executor.take`, `Executor.takeReport` and the `k` of
`Executor.work` each perform, in one critical section per call. A scheduler that refused leaves the pool as
it was, which is no transaction at all and needs no theorem. -/
theorem Aligned.takeReport (st : State α cap) (h : st.Aligned) (hw : st.pool.ring.WF)
    (s' : Scheduler) (hr : (st.pool.takeReport).item.isSome) (hs : st.sched.take = some s') :
    ({ st with pool := (st.pool.takeReport).pool, sched := s' } : State α cap).Aligned := by
  have hp : ((st.pool.takeReport).pool).inFlight + 1 = st.pool.inFlight :=
    takeReport_inFlight st.pool hw hr
  -- The scheduler's count is the one it just removed.
  have hs' : s' = { st.sched with work := st.sched.work - 1 } := by
    rw [Scheduler.take] at hs
    split at hs
    · exact (Option.some.inj hs).symm
    · exact absurd hs (by simp)
  unfold State.Aligned at h
  show s'.work = ((st.pool.takeReport).pool).inFlight
  rw [hs']
  dsimp only
  omega

/-- **Take without the parking machinery.** `some (some x)` when it took work, `some none` when the pool is
empty *and* stopping, `none` when it is empty but still running — so the caller knows to park.

This is the shape Tokio's worker loop has, and it is the shape a worker should have: take, and only park when
there was nothing to take. The take is one critical section and nothing else; parking is not on this path at
all. A take that returns nothing implies `inFlight = 0`, because `Pool.take` flushes an occupied LIFO slot
before serving the ring, so the predicate below re-checks exactly the condition this could not decide. -/
def Executor.tryTake (e : Executor α cap) : IO (Option (Option α)) :=
  e.state.atomically do
    let st ← get
    match st.pool.take with
    | (none, _) => return (if st.sched.stopping then some none else none)
    | (some x, p') =>
      match st.sched.take with
      | none    => return none
      | some s' => set ({ st with pool := p', sched := { s' with parked := 0 } }); return (some (some x))

/-- **One step of a worker: take work, or park until there is some.** The predicate is re-checked under
the same lock a submit notifies under, which is what makes the model's check-and-park atomicity real: a
worker that finds nothing parks *inside* this critical section rather than between two of them, so a wakeup
cannot be lost in the gap.

`none` means the pool was stopping. A take advances the pool and the scheduler together, exactly as
`Executor.take` does — the two halves of the alignment cannot come apart here either.

**The common case does not reach the park.** `tryTake` runs first, and only when it reports an empty pool that
is still running does this park — which is once per drained queue rather than once per item. -/
def Executor.work (e : Executor α cap) : IO (Option α) := do
  match ← e.tryTake with
  | some r => return r
  | none   =>
    e.state.atomicallyOnce e.cv
      (pred := do
        let st ← get
        if st.pool.inFlight ≠ 0 ∨ st.sched.stopping then return true
        else
          -- Nothing to take, so this worker is about to park — and it says so *while still holding the
          -- lock*, in the same critical section that will wait. A submit cannot slip between the check and
          -- the park, which is the whole content of the model's `park` having no transition while work is
          -- held. Guarded on `parked = 0` so a spurious wake does not record a second park for the same
          -- worker; the `k` below clears it. One worker is `parked := 1`, which is M3's single carrier.
          if st.sched.parked = 0 then
            set ({ st with sched := { st.sched with parked := 1 } })
          return false)
      (k := do
        let st ← get
        match st.pool.take with
        | (none, _) => return none
        | (some x, p') =>
          match st.sched.take with
          | none    => return none
          -- Waking to take work means the worker is no longer parked, in the same critical section as the
          -- take, so the state never shows a worker both parked and holding work.
          | some s' => set ({ st with pool := p', sched := { s' with parked := 0 } }); return (some x))

/-- **The whole state as the specification sees it**, for a client that needs more than the two counts:
`inFlight`, `taken` and `parked` all come from here. Using the projection rather than a bespoke accessor is
deliberate -- it is the same function the refinement is stated over, so a record read through it cannot
disagree with the model about what the implementation holds. -/
def Executor.snapshot (e : Executor α cap) : IO (Model.Pool α × Model.Sched) :=
  e.state.atomically do
    let st ← get
    return st.toModel

/-- What the executor currently holds, for an observer outside the critical section. -/
def Executor.observe (e : Executor α cap) : IO (Nat × Nat) :=
  e.state.atomically do
    let st ← get
    return (st.pool.inFlight, st.sched.parked)

end LeanIn.Sched
