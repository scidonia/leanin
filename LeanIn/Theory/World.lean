import Std

/-!
# The abstract machine

The state and transition relation of [`docs/primitive-theory.md`](../../docs/primitive-theory.md).
Ordinary Lean — no axioms, no `IO`, no threads. Everything here is a definition or a theorem.

Building it this way showed the theory document was slightly wrong about its own shape: most of what
it called "axioms" are **theorems about this relation**. What stays axiomatic is only the bridge in
`Bridge.lean` — the claim that a `Std` operation performs one of these transitions and nothing else.

## Shape

* `World` is the machine state: every lock, every condition variable, and a clock.
* `Act` is an action a thread may attempt.
* `step w a` is the (partial) effect of attempting `a` in `w`; `Step` is the relation it defines.

Preconditions are *decisions inside `step`*, returning `none` when violated. An action whose
precondition fails therefore has **no** transition, which is what makes A3 ("releasing a lock you do
not hold is undefined") a structural fact rather than a checked error.

## What is deliberately missing

There is **no queue of pending lock requests**. `std::mutex` has none, so neither does the model, and
that is why fairness is not merely unproven here but *inexpressible*: there is nothing a fairness
obligation could be stated against. See `reacquisition_while_others_wait`.
-/

namespace LeanIn

/-- The actor of a step: a **native** thread.

In v1 that means the scheduler's carrier or a waker thread — `WakerSpike` shows an external completion
handled on a pool worker, which takes the same mutex the carrier does. It never means a green task: two
tasks running on one carrier are one native actor, and no green task owns a mutex or parks. When green
tasks enter this model they need their own identity, distinct from this one. -/
abbrev Tid := Nat
abbrev LockId := Nat
abbrev CondvarId := Nat

/-- Point update on a total map. Defined here rather than taken from `Function.update`, so the model
carries its own two-line theory instead of depending on where those lemmas live. -/
def upd {α : Type} (f : Nat → α) (i : Nat) (v : α) : Nat → α := fun j => if j = i then v else f j

@[simp] theorem upd_self {α : Type} (f : Nat → α) (i : Nat) (v : α) : upd f i v i = v := by
  simp [upd]

@[simp] theorem upd_of_ne {α : Type} (f : Nat → α) {i j : Nat} (h : j ≠ i) (v : α) :
    upd f i v j = f j := by
  simp [upd, h]

/-- A lock: at most one owner. Mutual exclusion is *structural* — see `lock_has_one_owner`. -/
structure Lock where
  owner : Option Tid := none
deriving Inhabited, Repr

/-- A condition variable: a set of waiting threads, and **no payload**.

The absence of a payload is A5. A condition variable has no memory, so nothing here can record that a
notification happened — which is why every park/wake protocol must carry its own state. -/
structure Condvar where
  waiters : List Tid := []
deriving Inhabited, Repr

/-- The machine state. Locks and condition variables are total maps, so no bounds proofs arise;
identifiers that are never used simply stay free forever. -/
structure World where
  locks    : LockId → Lock := fun _ => {}
  condvars : CondvarId → Condvar := fun _ => {}
  /-- The model's notion of elapsed time, advanced by `tick`. -/
  clock    : Nat := 0
  /-- The last reading taken from the native clock, kept **apart from** `clock`.

They are different things, and conflating them loses the only property a budget needs. `clock` is model
time, moved by `tick`; this records what a read returned. Recording it is what makes successive readings
comparable — with only `n ≥ clock` against a clock that no read moves, two reads are related to nothing,
and "the clock never goes backwards" stays a property of the runtime that no theorem can use. -/
  lastSample : Option Nat := none
deriving Inhabited

/-- Two worlds agree on the clock state: model time, and the last sample taken.

Operations that do not read the clock must leave both alone. Without that, a reading before and a
reading after any other bridge call are related to nothing — the intervening operation is free to set
`lastSample` back to `none`, and the next reading's "never behind the previous sample" becomes vacuous.
Monotonicity across a budget would then be underivable despite each reading being monotone on its own. -/
def World.SameClock (w w' : World) : Prop := w'.clock = w.clock ∧ w'.lastSample = w.lastSample

/-- An action.

`spurious` exists because A4 permits it: a waiter may resume with no notification. There is no
`requestLock`, because an *unsuccessful* acquisition is a non-event — which is A1's absence of
fairness showing up as an absence of vocabulary. -/
inductive Act where
  | lock      (l : LockId) (t : Tid)
  | unlock    (l : LockId) (t : Tid)
  | wait      (c : CondvarId) (l : LockId) (t : Tid)
  /-- Waking one waiter, **naming it**: the runtime call names no waiter, so the choice is the
  action's, exactly as for `spurious`. -/
  | notifyOne (c : CondvarId) (t : Tid)
  | notifyAll (c : CondvarId)
  | spurious  (c : CondvarId) (t : Tid)
  /-- Time passing. Not an operation any thread performs; it exists so that "the clock advanced" is a
  statement the model can make, and so `tickless` worlds have a reason to differ. -/
  | tick
deriving DecidableEq, Repr

/-! ### Post-states, named so the theorems can state them -/

def afterLock (w : World) (l : LockId) (t : Tid) : World :=
  { w with locks := upd w.locks l { owner := some t } }

def afterUnlock (w : World) (l : LockId) : World :=
  { w with locks := upd w.locks l { owner := none } }

def afterWait (w : World) (c : CondvarId) (l : LockId) (t : Tid) : World :=
  { w with locks    := upd w.locks l { owner := none },
           condvars := upd w.condvars c { waiters := (w.condvars c).waiters ++ [t] } }

/-- Waking one waiter, **naming it**.

`notify_one` unblocks *one of* the threads waiting, and names none, so the model's action carries the
choice — exactly as `spurious` does. That is what makes the model's freedom match the runtime's: every
choice is a distinct transition, rather than the model silently picking the head and so claiming a fact
the machine does not provide. Waking a thread that is not enrolled removes nothing, which is the lost
notification of A5 and not an error. -/
def afterNotifyOne (w : World) (c : CondvarId) (t : Tid) : World :=
  { w with condvars := upd w.condvars c { waiters := (w.condvars c).waiters.erase t } }

def afterNotifyAll (w : World) (c : CondvarId) : World :=
  { w with condvars := upd w.condvars c { waiters := [] } }

/-- The resume, from the waiter's side: it stops being a waiter.

`filter` rather than `erase`, because `List.erase` removes only the **first** occurrence and this model
does not require `waiters` to be duplicate-free — a thread can be enrolled twice by the transitions as
written (`wait`, `lock`, `wait`). With `erase`, a doubly-enrolled thread that wakes spuriously stays a
waiter, which is a state no machine can be in. Filtering maps the set-like reading directly, so
de-enrolment holds unconditionally.

**Open question, not settled here:** whether to exclude double enrolment at its source instead, by
giving `wait` the precondition that its caller is not already enrolled. -/
def afterSpurious (w : World) (c : CondvarId) (t : Tid) : World :=
  { w with condvars := upd w.condvars c { waiters := (w.condvars c).waiters.filter (· != t) } }

/-- The effect of an action, or `none` if its precondition does not hold. -/
def step (w : World) : Act → Option World
  | .lock l t      => if (w.locks l).owner = none then some (afterLock w l t) else none
  | .unlock l t    => if (w.locks l).owner = some t then some (afterUnlock w l) else none
  | .wait c l t    => if (w.locks l).owner = some t ∧ t ∉ (w.condvars c).waiters
                      then some (afterWait w c l t) else none
  | .notifyOne c t => some (afterNotifyOne w c t)
  | .notifyAll c   => some (afterNotifyAll w c)
  | .spurious c t  => if t ∈ (w.condvars c).waiters then some (afterSpurious w c t) else none
  | .tick          => some { w with clock := w.clock + 1 }

/-- The transition relation. One constructor, so every proof below is a `simp` on `step`. -/
def Step (w : World) (a : Act) (w' : World) : Prop := step w a = some w'

/-- **The waiter invariant: no thread is enrolled twice on one condvar.**

A thread is either parked or running, so a second enrolment would mean it was both. **The model does not
enforce that**, and this is the place to say so: the transition relation is an over-approximation, and a
parked carrier can still take an action — nothing in `step` prevents `.lock` after `.wait`. What the
machine enforces is stated where it is needed, as `wait`'s precondition that its caller is not already
enrolled, and that is why the invariant survives; it is not a general rule about parked actors. The model
*could*
represent it — the sequence `lock 0 by 0 → wait 0 by 0 → lock 0 by 0 → wait 0 by 0` reaches
`waiters = [0, 0]`, which `nix develop -c lake exe dynamics` reports as reachable — and that is what made
a spurious waiter's removal ambiguous: `List.erase` removes only the first occurrence, so one of the two
survived and the thread stayed enrolled after waking. With this invariant stated, `erase` removes *the*
occurrence and the removal is exact. -/
def World.WaitersNodup (w : World) : Prop := ∀ c, (w.condvars c).waiters.Nodup

/-- **Every transition preserves the waiter invariant.** Only `wait`, `notifyOne`, `notifyAll` and
`spurious` touch a waiter set at all, and `wait` is the one that could break the invariant — which is why
its precondition now includes that its caller is not already enrolled. A thread cannot be parked twice,
so the step that would represent it is not available. -/
theorem step_preserves_nodup {w : World} {a : Act} {w' : World}
    (hw : w.WaitersNodup) (h : Step w a w') : w'.WaitersNodup := by
  unfold Step at h
  cases a with
  | lock l t =>
      simp only [step] at h
      split at h
      · injection h with h; subst h; exact hw
      · exact absurd h (by simp)
  | unlock l t =>
      simp only [step] at h
      split at h
      · injection h with h; subst h; exact hw
      · exact absurd h (by simp)
  | tick =>
      injection h with h; subst h; exact hw
  | wait c l t =>
      simp only [step] at h
      split at h
      · rename_i hp
        injection h with h; subst h
        intro c'
        unfold World.WaitersNodup at hw
        by_cases hcc : c' = c
        · subst hcc
          simp only [afterWait, upd_self]
          exact List.nodup_append.mpr
            ⟨hw c', by simp, by
              intro a ha b hb hEq
              exact hp.2 ((hEq.trans (List.mem_singleton.mp hb)) ▸ ha)⟩
        · simp only [afterWait, upd_of_ne w.condvars hcc]
          exact hw c'
      · exact absurd h (by simp)
  | notifyOne c t =>
      injection h with h; subst h
      intro c'
      unfold World.WaitersNodup at hw
      by_cases hcc : c' = c
      · subst hcc; simp only [afterNotifyOne, upd_self]
        exact (hw c').erase t
      · simp only [afterNotifyOne, upd_of_ne w.condvars hcc]
        exact hw c'
  | notifyAll c =>
      injection h with h; subst h
      intro c'
      by_cases hcc : c' = c
      · subst hcc; simp [afterNotifyAll]
      · simp only [afterNotifyAll, upd_of_ne w.condvars hcc]
        exact hw c'
  | spurious c t =>
      simp only [step] at h
      split at h
      · injection h with h; subst h
        intro c'
        unfold World.WaitersNodup at hw
        by_cases hcc : c' = c
        · subst hcc; simp only [afterSpurious, upd_self]
          exact (hw c').filter (· != t)
        · simp only [afterSpurious, upd_of_ne w.condvars hcc]
          exact hw c'
      · exact absurd h (by simp)

/-! ### A1 — mutual exclusion is structural -/

/-- A lock holds at most one owner, by construction. Mutual exclusion is not assumed here; it follows
from `Lock` being a record with a single `Option Tid`. The honest reading: `std::mutex` does the work,
and the model simply cannot represent a state in which two threads hold one lock. -/
theorem lock_has_one_owner (lk : Lock) {t₁ t₂ : Tid}
    (h₁ : lk.owner = some t₁) (h₂ : lk.owner = some t₂) : t₁ = t₂ := by
  rw [h₁] at h₂
  exact Option.some.inj h₂

/-- A1 (acquisition half): a successful `lock` is observed as ownership. -/
theorem lock_gives_ownership {w : World} {l : LockId} {t : Tid}
    (h : (w.locks l).owner = none) : Step w (.lock l t) (afterLock w l t) := by
  simp [Step, step, h]

/-- A1 (release half): after `unlock` the lock is free, so a later `lock` cannot fail. Visibility
proper belongs to the bridge — it is about the memory model, not the relation. -/
theorem unlock_frees {w : World} {l : LockId} {t : Tid}
    (h : (w.locks l).owner = some t) : Step w (.unlock l t) (afterUnlock w l) := by
  simp [Step, step, h]

/-- A3: there is no transition for releasing a lock you do not hold. Preconditions are not checked
here — they are unrepresentable. -/
theorem unlock_without_ownership_has_no_transition {w : World} {l : LockId} {t : Tid}
    (h : (w.locks l).owner ≠ some t) : step w (.unlock l t) = none := by
  simp [step, h]

/-! ### A5 — no notification memory -/

/-- **A5, proved.** `notifyOne` with no waiter changes nothing.

This is the theorem that forces every park/wake protocol to carry its own state: the primitive cannot
remember that a notification was issued, so a worker that parks after a notify sleeps forever unless
the state it re-checks under the same lock says otherwise. -/
theorem notifyOne_no_waiters {w : World} {c : CondvarId} {t : Tid}
    (h : (w.condvars c).waiters = []) : ((afterNotifyOne w c t).condvars c).waiters = [] := by
  simp [afterNotifyOne, h]

/-- The **affirmative control** for `notifyOne_no_waiters`: the same detector must fire when the thing
is present, or a marker that matches nothing passes forever. Here a waiter really is removed. -/
theorem notifyOne_removes_waiter {w : World} {c : CondvarId} {t : Tid}
    (h : (w.condvars c).waiters = [t]) : ((afterNotifyOne w c t).condvars c).waiters = [] := by
  simp [afterNotifyOne, h]

/-- The control from the other side: a non-empty waiter list is genuinely shortened, and by **the
named waiter** — the other one is left. Two waiters, one woken, one still enrolled. -/
theorem notifyOne_removes_exactly_one {w : World} {c : CondvarId} {t₁ t₂ : Tid}
    (h : (w.condvars c).waiters = [t₁, t₂]) :
    ((afterNotifyOne w c t₁).condvars c).waiters = [t₂] := by
  simp [afterNotifyOne, h]

/-- `notifyAll` clears the set outright, which is what the shutdown path relies on. -/
theorem notifyAll_clears {w : World} {c : CondvarId} :
    ((afterNotifyAll w c).condvars c).waiters = [] := by
  simp [afterNotifyAll]

/-! ### A4 — spurious wakeups are permitted -/

/-- **A4, proved.** A waiter may resume with no notification at all, so any protocol that reads `wait`
as "returns only when notified" is wrong and `waitUntil`-shaped re-checking is mandatory. -/
theorem spurious_wakeup_permitted {w : World} {c : CondvarId} {t : Tid}
    (h : t ∈ (w.condvars c).waiters) : Step w (.spurious c t) (afterSpurious w c t) := by
  simp [Step, step, h]

/-- The control for A4: `wait` is the *only* other way into the waiter set, and it requires holding
the lock. So waiters appear without a notification and disappear without one — neither direction is
constrained, which is exactly why predicates must be re-checked. -/
theorem wait_parks_and_releases {w : World} {c : CondvarId} {l : LockId} {t : Tid}
    (h : (w.locks l).owner = some t) (hn : t ∉ (w.condvars c).waiters) :
    Step w (.wait c l t) (afterWait w c l t) := by
  simp [Step, step, h, hn]

/-! ### A4 — the cycle a `wait` call spans

A runtime `wait` is one operation to its caller and three model steps to this model: park (release and
enrol), resume, re-acquire. These three theorems are what a `wait` obligation has to rest on. -/

/-- **Parking releases the lock** — which is why the condition can become reachable at all: the step
that enrols the waiter also gives the lock up. This is the fact that stops `wait` corresponding to a
single model step. -/
theorem afterWait_releases {w : World} {c : CondvarId} {l : LockId} {t : Tid} :
    ((afterWait w c l t).locks l).owner = none := by
  simp [afterWait]

/-- **The whole cycle, as the model reaches it**: park, resume, re-acquire. The endpoint is what the
caller observes on return — it holds the lock again, and it is no longer a waiter. -/
theorem wait_cycle_reachable {w : World} {c : CondvarId} {l : LockId} {t : Tid}
    (h : (w.locks l).owner = some t) (hn : t ∉ (w.condvars c).waiters) :
    ∃ w₁ w₂ w₃ : World,
      Step w (.wait c l t) w₁ ∧ Step w₁ (.spurious c t) w₂ ∧ Step w₂ (.lock l t) w₃ ∧
      (w₃.locks l).owner = some t ∧ t ∉ (w₃.condvars c).waiters := by
  refine ⟨afterWait w c l t, afterSpurious (afterWait w c l t) c t,
          afterLock (afterSpurious (afterWait w c l t) c t) l t, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Step, step, h, hn]
  · simp [Step, step, afterWait, List.mem_append]
  · simp [Step, step, afterWait, afterSpurious]
  · simp [afterLock, upd_self]
  · simp [afterLock, afterSpurious, List.mem_filter]

/-- **The control**: re-acquisition is possible for *anyone*, not compelled for the waiter, because
parking left the lock free. So `owner = some t` on return is a scheduler decision, and a `wait`
obligation must identify the re-acquiring thread rather than let the matching endpoint stand in for
it. -/
theorem reacquisition_is_anyone {w : World} {c : CondvarId} {l : LockId} {t t' : Tid}
    (h : (w.locks l).owner = some t) (hn : t ∉ (w.condvars c).waiters) :
    ∃ w₁ w₂ : World,
      Step w (.wait c l t) w₁ ∧ Step w₁ (.lock l t') w₂ ∧ (w₂.locks l).owner = some t' := by
  refine ⟨afterWait w c l t, afterLock (afterWait w c l t) l t', ?_, ?_, ?_⟩
  · simp [Step, step, h, hn]
  · simp [Step, step, afterWait]
  · simp [afterLock, upd_self]

/-! ### A1 — no fairness, and why it is structural -/

/-- Both threads can acquire first from the same state: no interleaving is excluded. This is the
positive form of "no fairness". -/
theorem both_orders_permitted {w : World} {l : LockId} {t₁ t₂ : Tid}
    (h : (w.locks l).owner = none) :
    (∃ w', Step w (.lock l t₁) w') ∧ (∃ w', Step w (.lock l t₂) w') :=
  ⟨⟨_, lock_gives_ownership h⟩, ⟨_, lock_gives_ownership h⟩⟩

/-- One thread acquires and releases repeatedly while another never does. The model has **no queue of
pending requests**, so there is nothing a starvation-freedom obligation could be stated against:
"no fairness" is a property of the model's *shape*, not a lemma that could be strengthened later
without changing the shape. -/
theorem reacquisition_while_others_wait {w : World} {l : LockId} {t : Tid}
    (h : (w.locks l).owner = none) :
    ∃ w₁ w₂ w₃ : World,
      Step w (.lock l t) w₁ ∧ Step w₁ (.unlock l t) w₂ ∧ Step w₂ (.lock l t) w₃ := by
  refine ⟨afterLock w l t, afterUnlock (afterLock w l t) l,
          afterLock (afterUnlock (afterLock w l t) l) l t, ?_, ?_, ?_⟩
  · simp [Step, step, h]
  · simp [Step, step, afterLock, afterUnlock]
  · simp [Step, step, afterLock, afterUnlock]

/-! ### Vacuity checks

Every theorem above is conditional, so each hypothesis must be shown to be *inhabited* — otherwise the
theorems are true of nothing — and each predicate must be shown to *distinguish*, or a marker that
matches nothing passes forever. These are the model-level controls. -/

/-- The lock-free premise is inhabited. -/
example : ∃ w : World, (w.locks 0).owner = none := ⟨default, rfl⟩

/-- …and so is its negation, so the predicate distinguishes. -/
example : ∃ w : World, (w.locks 0).owner ≠ none :=
  ⟨afterLock default 0 0, by simp [afterLock]⟩

/-- An empty waiter set is inhabited… -/
example : ∃ w : World, (w.condvars 0).waiters = [] := ⟨default, rfl⟩

/-- …and so is a non-empty one, so `notifyOne`'s two cases are both reachable. -/
example : ∃ w : World, (w.condvars 0).waiters ≠ [] :=
  ⟨afterWait default 0 0 0, by simp [afterWait]⟩

/-- The clock can advance, so `tick` is not a dead action. -/
example : ∃ w : World, w.clock = 1 :=
  ⟨{ (default : World) with clock := 1 }, rfl⟩

end LeanIn
