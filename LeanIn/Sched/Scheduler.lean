import LeanIn.Model.Scheduler

/-!
# The wake protocol, as the implementation keeps it

`LeanIn.Model.Sched` is the specification; this is the state an executor actually holds, with `toModel` the
projection the refinement is stated about. The two carry the same four fields, and that is deliberate rather
than lazy: the implementation will grow a mutex and a condvar around them, and the projection is what keeps
"the implementation does what the model does" statable once it does.

**The one thing to read carefully is `enqueue`.** Adding work and unparking a worker are a *single* step
here, because they are a single step in the model and that inseparability is the entire content of
`reachable_live`. `Model.Sched.enqueueWithoutWaking` exists as the plausible-and-wrong alternative; it is not
mirrored here because an implementation has no use for it — a version of `enqueue` that forgets to wake is a
bug, not a second operation.

Everything real about the protocol is *not* in these functions: it is in where the lock is taken and
released. This structure is the state under that lock, and the carrier is what will hold it.
-/

namespace LeanIn.Sched

/-- The scheduler state: work available, workers parked, workers in total, and whether shutdown has been
observed. -/
structure Scheduler where
  /-- Work available anywhere: every worker's ring, LIFO slot, and the inject queue. -/
  work     : Nat := 0
  /-- Workers currently parked. -/
  parked   : Nat := 0
  /-- Workers in total. Constant: workers neither arrive nor leave. -/
  total    : Nat := 0
  /-- Set by `stop`. -/
  stopping : Bool := false
deriving Inhabited, Repr

/-- Well-formedness: at least one worker, and not more parked than exist. -/
def Scheduler.WF (s : Scheduler) : Prop := 0 < s.total ∧ s.parked ≤ s.total

/-- **No lost wakeup.** If there is work, at least one worker is not parked. -/
def Scheduler.Live (s : Scheduler) : Prop := s.work = 0 ∨ s.parked < s.total

/-- A fresh scheduler: `n` workers, none parked, no work. -/
def Scheduler.initial (n : Nat) : Scheduler := { work := 0, parked := 0, total := n }

/-- **The projection.** The same four fields, read as the specification describes them. -/
def Scheduler.toModel (s : Scheduler) : Model.Sched :=
  { work := s.work, parked := s.parked, total := s.total, stopping := s.stopping }

/-! ### The protocol -/

/-- **Enqueue, correctly.** Work is added *and* a parked worker is unparked, as one step.

The two halves are not separable — that is `reachable_live` — and in an executor it is one critical
section: check-and-park under the same lock that an enqueue wakes under, or the wakeup is lost between the
check and the park. -/
def Scheduler.enqueue (s : Scheduler) : Scheduler :=
  { s with work := s.work + 1, parked := if 0 < s.parked then s.parked - 1 else 0 }

/-- A worker parks. **No transition unless there is no work and a worker is still running** — the encoding
of checking the work state and parking under the same lock. `none` is a refused park, not a failed one. -/
def Scheduler.park (s : Scheduler) : Option Scheduler :=
  if s.work = 0 ∧ s.parked < s.total then some { s with parked := s.parked + 1 } else none

/-- A worker completes one item of work. -/
def Scheduler.take (s : Scheduler) : Option Scheduler :=
  if 0 < s.work then some { s with work := s.work - 1 } else none

/-- Shutdown. -/
def Scheduler.stop (s : Scheduler) : Scheduler := { s with stopping := true }

/-! ### Agreement with the specification

Stated over `toModel` so that the refinement does not rest on the two structures happening to carry the same
fields today. `park` and `take` are `Option`-valued, so their agreement is `Option.map` rather than equality
of the states alone: a refused park must be refused on both sides, which is a claim about `none` as much as
about `some`. -/

theorem toModel_initial (n : Nat) : (Scheduler.initial n).toModel = Model.Sched.initial n := by
  simp [Scheduler.initial, Scheduler.toModel, Model.Sched.initial]

theorem toModel_enqueue (s : Scheduler) : (s.enqueue).toModel = (s.toModel).enqueue := by
  by_cases h : 0 < s.parked <;>
    simp [Scheduler.enqueue, Scheduler.toModel, Model.Sched.enqueue, h]

theorem toModel_park (s : Scheduler) : (s.park).map Scheduler.toModel = (s.toModel).park := by
  by_cases h : s.work = 0 ∧ s.parked < s.total <;>
    simp [Scheduler.park, Scheduler.toModel, Model.Sched.park, h]

theorem toModel_take (s : Scheduler) : (s.take).map Scheduler.toModel = (s.toModel).take := by
  by_cases h : 0 < s.work <;>
    simp [Scheduler.take, Scheduler.toModel, Model.Sched.take, h]

theorem toModel_stop (s : Scheduler) : (s.stop).toModel = (s.toModel).stop := by
  simp [Scheduler.stop, Scheduler.toModel, Model.Sched.stop]

/-- **The invariants transfer.** They are stated over the same fields, so the projection carries them
across unchanged — which is what lets the model's `reachable_live` be read as a claim about the
implementation's state. -/
theorem toModel_WF (s : Scheduler) (h : s.WF) : s.toModel.WF := by
  simp [Scheduler.WF, Scheduler.toModel, Model.Sched.WF] at h ⊢
  exact h

theorem toModel_Live (s : Scheduler) (h : s.Live) : s.toModel.Live := by
  simp [Scheduler.Live, Scheduler.toModel, Model.Sched.Live] at h ⊢
  exact h

end LeanIn.Sched
