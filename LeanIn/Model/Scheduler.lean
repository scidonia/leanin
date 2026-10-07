import Std

/-!
# The scheduler, and no lost wakeup

The wake protocol of [`docs/interface.md`](../../docs/interface.md) §3, as Lean. The state is
abstracted to exactly what the protocol cares about — how much work exists, how many workers are
parked, how many there are at all — because the property is about the *protocol*, not the payload.
The payload side is `LeanIn.Model.Pool`; `work` here is the sum of every worker's `inFlight` plus the
inject queue.

## The property

**No lost wakeup**: no reachable state has work available while every worker is parked. `reachable_live`
below.

## Why it is not vacuous

A property like this is easy to state and easy to make meaningless. Two things keep it honest:

* `park` has **no transition** unless `work = 0` and a worker is still running. That is the model's
  encoding of "check the work state and park under the same lock" — the check is not a separate step
  that could be interleaved with.
* `enqueue` unparks a parked worker **in the same step** as it adds the work. The control
  `enqueueWithoutWaking_breaks_live` shows this is load-bearing: a plausible enqueue that adds work and
  leaves the waking to a separate step *does* destroy the invariant.

That second point is A5 showing through. `std::condition_variable` has no memory — proved as
`notifyOne_no_waiters` in `Theory/World.lean` — so a notification that lands before the worker parks is
lost. The only way to be safe is for the unparking to be part of the enqueue, which is what the model
now says.
-/

namespace LeanIn

/-- The scheduler state, abstracted to what the wake protocol needs. -/
structure Sched where
  /-- Work available anywhere: every worker's ring, LIFO slot, and the inject queue. -/
  work     : Nat := 0
  /-- Workers currently parked. -/
  parked   : Nat := 0
  /-- Workers in total. Constant: workers neither arrive nor leave in this model. -/
  total    : Nat := 0
  /-- Set by `stop`. -/
  stopping : Bool := false
deriving Inhabited, Repr

/-- Well-formedness: there is at least one worker, and not more parked than exist. -/
def Sched.WF (s : Sched) : Prop := 0 < s.total ∧ s.parked ≤ s.total

/-- **No lost wakeup.** If there is work, at least one worker is not parked. -/
def Sched.Live (s : Sched) : Prop := s.work = 0 ∨ s.parked < s.total

/-- A fresh scheduler: `n` workers, none parked, no work. -/
def Sched.initial (n : Nat) : Sched := { work := 0, parked := 0, total := n }

/-! ### The protocol -/

/-- **Enqueue, correctly.** Work is added *and* a parked worker is unparked, as one step.

The two halves are not separable: that is the whole content of `reachable_live`. -/
def Sched.enqueue (s : Sched) : Sched :=
  { s with work := s.work + 1, parked := if 0 < s.parked then s.parked - 1 else 0 }

/-- **Enqueue, naively.** Adds the work and leaves the waking to some later step. Plausible, and
wrong — see `enqueueWithoutWaking_breaks_live`. -/
def Sched.enqueueWithoutWaking (s : Sched) : Sched := { s with work := s.work + 1 }

/-- A worker parks. **No transition unless there is no work and a worker is still running** — the
encoding of checking the work state and parking under the same lock. -/
def Sched.park (s : Sched) : Option Sched :=
  if s.work = 0 ∧ s.parked < s.total then some { s with parked := s.parked + 1 } else none

/-- A worker completes one item of work. -/
def Sched.take (s : Sched) : Option Sched :=
  if 0 < s.work then some { s with work := s.work - 1 } else none

/-- Shutdown. -/
def Sched.stop (s : Sched) : Sched := { s with stopping := true }

/-! ### The invariant is preserved -/

theorem enqueue_live {s : Sched} (h : s.WF) : s.enqueue.Live := by
  obtain ⟨htot, hle⟩ := h
  unfold Sched.enqueue Sched.Live
  by_cases hp : 0 < s.parked
  · simp only [hp, ite_true]
    omega
  · simp only [hp, ite_false]
    omega

/-- A successful park yields a `Live` state — with no hypothesis needed, because `park` requires
`work = 0`, which is the left disjunct outright. -/
theorem park_live {s s' : Sched} (hs : s.park = some s') : s'.Live := by
  unfold Sched.park at hs
  by_cases hc : s.work = 0 ∧ s.parked < s.total
  · rw [ite_eq_left hc] at hs
    obtain ⟨hwork, _⟩ := hc
    injection hs with hseq
    have hw : s'.work = s.work := by simp only [← hseq]
    have hp : s'.parked = s.parked + 1 := by simp only [← hseq]
    have ht : s'.total = s.total := by simp only [← hseq]
    unfold Sched.Live
    rw [hw, hp, ht] at *
    omega
  · rw [ite_eq_right hc] at hs
    exact absurd hs (by simp)

theorem take_live {s s' : Sched} (h : s.Live) (hs : s.take = some s') : s'.Live := by
  unfold Sched.take at hs
  by_cases hc : 0 < s.work
  · rw [ite_eq_left hc] at hs
    injection hs with hseq
    have hw : s'.work = s.work - 1 := by simp only [← hseq]
    have hp : s'.parked = s.parked := by simp only [← hseq]
    have ht : s'.total = s.total := by simp only [← hseq]
    unfold Sched.Live at h ⊢
    rw [hw, hp, ht] at *
    omega
  · rw [ite_eq_right hc] at hs
    exact absurd hs (by simp)

theorem stop_live {s : Sched} (h : s.Live) : s.stop.Live := h

theorem enqueue_wf {s : Sched} (h : s.WF) : s.enqueue.WF := by
  obtain ⟨htot, hle⟩ := h
  unfold Sched.enqueue Sched.WF
  by_cases hp : 0 < s.parked
  · simp only [hp, ite_true]
    omega
  · simp only [hp, ite_false]
    omega

theorem park_wf {s s' : Sched} (h : s.WF) (hs : s.park = some s') : s'.WF := by
  obtain ⟨htot, hle⟩ := h
  unfold Sched.park at hs
  by_cases hc : s.work = 0 ∧ s.parked < s.total
  · rw [ite_eq_left hc] at hs
    obtain ⟨_, hlt⟩ := hc
    injection hs with hseq
    have hp : s'.parked = s.parked + 1 := by simp only [← hseq]
    have ht : s'.total = s.total := by simp only [← hseq]
    unfold Sched.WF
    rw [hp, ht] at *
    omega
  · rw [ite_eq_right hc] at hs
    exact absurd hs (by simp)

theorem take_wf {s s' : Sched} (h : s.WF) (hs : s.take = some s') : s'.WF := by
  unfold Sched.take at hs
  by_cases hc : 0 < s.work
  · rw [ite_eq_left hc] at hs
    injection hs with hseq
    have hp : s'.parked = s.parked := by simp only [← hseq]
    have ht : s'.total = s.total := by simp only [← hseq]
    unfold Sched.WF at h ⊢
    rw [hp, ht] at *
    exact h
  · rw [ite_eq_right hc] at hs
    exact absurd hs (by simp)

/-! ### Reachability

"Reachable" is the right strength: the invariant is not claimed of arbitrary well-formed states — a
state with work and every worker parked is well-formed and would be a lost wakeup — only of states the
protocol can actually produce. -/

inductive Reachable : Sched → Prop where
  | init (n : Nat) (h : 0 < n) : Reachable (Sched.initial n)
  | enqueue {s : Sched} : Reachable s → Reachable s.enqueue
  | park {s s' : Sched} : Reachable s → s.park = some s' → Reachable s'
  | take {s s' : Sched} : Reachable s → s.take = some s' → Reachable s'
  | stop {s : Sched} : Reachable s → Reachable s.stop

theorem reachable_wf_live {s : Sched} (h : Reachable s) : s.WF ∧ s.Live := by
  induction h with
  | init n hn =>
    exact ⟨by simp only [Sched.initial, Sched.WF]; omega,
           by simp [Sched.initial, Sched.Live]⟩
  | enqueue hrec ih => exact ⟨enqueue_wf ih.1, enqueue_live ih.1⟩
  | park hrec hs ih => exact ⟨park_wf ih.1 hs, park_live hs⟩
  | take hrec hs ih => exact ⟨take_wf ih.1 hs, take_live ih.2 hs⟩
  | stop hrec ih => exact ih

theorem reachable_wf {s : Sched} (h : Reachable s) : s.WF := (reachable_wf_live h).1

/-- **No lost wakeup.** Every reachable state has either no work, or a worker that is not parked. -/
theorem reachable_live {s : Sched} (h : Reachable s) : s.Live := (reachable_wf_live h).2

/-! ### Vacuity and the control

`Live` must distinguish, and the protocol's unpark must be load-bearing. -/

/-- `Live` is inhabited. -/
example : (Sched.initial 4).Live := by simp [Sched.initial, Sched.Live]

/-- …and so is its negation, so `Live` is not true of everything. -/
example : ∃ s : Sched, ¬ s.Live := ⟨{ work := 1, parked := 4, total := 4 }, by simp [Sched.Live]⟩

/-- That state is well-formed — so `Live` is genuinely stronger than `WF`, and reachability is doing
real work rather than being implied by well-formedness. -/
example : ({ work := 1, parked := 4, total := 4 } : Sched).WF := by simp [Sched.WF]

/-- **The control.** A well-formed, `Live` state whose `Live`ness a plausible enqueue destroys —
because it adds the work and leaves the waking to a separate step. This is what makes the unpark in
`enqueue` load-bearing, and it is A5 in protocol form: the notification has no memory, so the unpark
cannot be deferred. -/
theorem enqueueWithoutWaking_breaks_live :
    ∃ s : Sched, s.WF ∧ s.Live ∧ ¬ s.enqueueWithoutWaking.Live :=
  ⟨{ work := 0, parked := 4, total := 4 },
   by simp [Sched.WF],
   by simp [Sched.Live],
   by simp [Sched.enqueueWithoutWaking, Sched.Live]⟩

/-- `park` really does refuse when there is work: the check is not advisory. -/
example : ({(default : Sched) with work := 1, parked := 0, total := 4}).park = none := by
  simp [Sched.park]

/-- …and it really does park when there is none, or the refusal above would be vacuous. -/
example : ({(default : Sched) with work := 0, parked := 0, total := 4}).park
            = some {(default : Sched) with work := 0, parked := 1, total := 4} := by
  simp [Sched.park]

/-- `take` refuses when there is no work — the mirror of `park`. -/
example : ({(default : Sched) with work := 0}).take = none := by simp [Sched.take]

-- The audit: the protocol's theorems rest on nothing beyond Lean's own axioms.
#print axioms LeanIn.reachable_live
#print axioms LeanIn.enqueue_live

end LeanIn
