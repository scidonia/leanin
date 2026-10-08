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
halves must not come apart through. **Its preservation is owed, not proved**: the transactions below are
*written* to respect it, and nothing yet checks that they do. It is the same equation
`tests/ModelOracle.lean` checks after every step of its script, which is where the check currently lives.

The carrier loop, the waker and the records are not here. This is the state and its critical sections.
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

def Executor.new (α : Type) (cap : Nat) (workers : Nat) : IO (Executor α cap) := do
  return { state := ← Std.Mutex.new { pool := emptyPool α cap, sched := Scheduler.initial workers } }

/-- Submit, or an external event delivering work: the pool takes it *and* the scheduler records it, as one
step. Reading `inFlight` afterwards is the work the pool holds. -/
def Executor.submit (e : Executor α cap) (x : α) : IO Unit :=
  e.state.atomically do
    let st ← get
    set ({ st with pool := st.pool.submit x, sched := st.sched.enqueue })

/-- Take one item of work. The pool and the scheduler advance together, or neither does — a pool that
returned a task while the scheduler removed no work would break `Aligned`, and one lock is what makes that
unreachable rather than merely unlikely. -/
def Executor.take (e : Executor α cap) : IO (Option α) :=
  e.state.atomically do
    let st ← get
    match st.pool.take with
    | (none, _) => return none
    | (some x, p') =>
      match st.sched.take with
      | none    => return none
      | some s' => set ({ st with pool := p', sched := s' }); return (some x)

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

theorem Aligned.submit_of_room (st : State α cap) (h : st.Aligned) (x : α)
    (hroom : st.pool.ring.size < cap) :
    ({ st with pool := st.pool.submit x, sched := st.sched.enqueue } : State α cap).Aligned := by
  have hp : (st.pool.submit x).inFlight = st.pool.inFlight + 1 :=
    inFlight_submit_of_room st.pool x hroom
  unfold State.Aligned at h ⊢
  show (st.sched.enqueue).work = (st.pool.submit x).inFlight
  rw [hp]
  simp only [Scheduler.enqueue]
  omega

/-- What the executor currently holds, for an observer outside the critical section. -/
def Executor.observe (e : Executor α cap) : IO (Nat × Nat) :=
  e.state.atomically do
    let st ← get
    return (st.pool.inFlight, st.sched.parked)

end LeanIn.Sched
