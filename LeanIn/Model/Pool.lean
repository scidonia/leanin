import Std

/-!
# The pool model

The pure model the interface of [`docs/interface.md`](../../docs/interface.md) is stated against, and
the shape the concurrent implementation must refine (D5).

This is not `List α` dressed up. The interesting content is the *worker shape* Tokio actually uses
(`docs/tokio-map.md` §2): a bounded FIFO ring, a one-slot LIFO buffer with a per-tick allowance, and a
shared inject queue that receives overflow. With those, "no work is lost" stops being obvious and
becomes a conservation law with a proof — which is the point, since Tokio asserts it at runtime
(`queue.rs:571`, a non-empty queue at drop is a bug) rather than proving it.

## Where the fields come from

| Field | Tokio |
|---|---|
| `ring`, `cap` | the 256-slot local queue, `push_back` at the back and `pop` at the front — **FIFO**, not a LIFO deque |
| `lifo`, `lifoPolls`, `lifoCap` | the LIFO slot and `MAX_LIFO_POLLS_PER_TICK = 3` (`worker.rs:265`) |
| `inject` | the overflow destination (`push_overflow` moves half the ring there, `queue.rs:253`) |
| `pushed`, `taken` | bookkeeping for the conservation law; not in Tokio, and the reason it can only assert |

## What is modelled and what is not

Modelled: ordering, capacity, overflow, the LIFO allowance, and the *flush* that stops the allowance
stranding work. Not modelled: the mutex, the ticket, memory ordering — those are `Theory/Bridge.lean`'s
business. A single `Pool` here is what one worker sees under its own lock.
-/

namespace LeanIn

-- The pure model lives under `LeanIn.Model`, matching its file path, because M3's implementation is
-- `LeanIn.Sched`: a model structure declared directly under `LeanIn` would share that namespace with it,
-- which is what happened silently until the collision was looked for.
namespace Model

structure Pool (α : Type) where
  /-- The bounded FIFO ring: submitted at the back, taken from the front. -/
  ring      : List α := []
  /-- The one-slot LIFO buffer. Owner-local, never stolen. -/
  lifo      : Option α := none
  /-- LIFO polls used in the current tick. -/
  lifoPolls : Nat := 0
  /-- The shared queue receiving overflow. Unbounded. -/
  inject    : List α := []
  /-- Total submitted. -/
  pushed    : Nat := 0
  /-- Total taken, by owner or thief. -/
  taken     : Nat := 0
  /-- Ring capacity. 256 in Tokio; any value ≥ 2 here. -/
  cap       : Nat := 256
  /-- LIFO polls allowed per tick. 3 in Tokio. -/
  lifoCap   : Nat := 3
deriving Inhabited, Repr

/-- The all-empty pool, written out field by field so that examples reduce — `default` does not
unfold, which silently turns a vacuity check into an unprovable goal. -/
def emptyPool (α : Type) : Pool α :=
  { ring := [], lifo := none, lifoPolls := 0, inject := [],
    pushed := 0, taken := 0, cap := 256, lifoCap := 3 }

/-- Work currently held somewhere: ring, LIFO slot, or inject. -/
def Pool.inFlight (p : Pool α) : Nat :=
  p.ring.length + (if p.lifo.isSome then 1 else 0) + p.inject.length

/-- **No lost work.** Everything ever submitted is either still held or was taken. This is Tokio's
runtime assertion, as an equation. -/
def Pool.Consistent (p : Pool α) : Prop := p.inFlight + p.taken = p.pushed

/-- Work is present somewhere. -/
def Pool.HasWork (p : Pool α) : Prop := p.ring ≠ [] ∨ p.lifo.isSome ∨ p.inject ≠ []

/-- The ring stays within capacity. -/
def Pool.Bounded (p : Pool α) : Prop := p.ring.length ≤ p.cap

/-! ### Taking -/

/-- The owner's take, ignoring the LIFO allowance: ring first, then inject. A thief uses this too,
which is where "the LIFO slot is never stolen" is expressed — this function cannot see `p.lifo`. -/
def Pool.takeFromRing (p : Pool α) : Option α × Pool α :=
  match p.ring with
  | x :: rest => (some x, { p with ring := rest, taken := p.taken + 1 })
  | []        => match p.inject with
    | x :: rest => (some x, { p with inject := rest, taken := p.taken + 1 })
    | []        => (none, p)

/-- The owner's take.

The LIFO slot is preferred while the tick's allowance lasts. **When the allowance runs out with a task
still in the slot, the slot is flushed to `inject` before the ring is consulted** — otherwise the
allowance could strand it, which is the same hazard `worker.rs:479` avoids when a worker gives up its
core. The proof of `take_returns_if_present` is what says the flush is doing its job. -/
def Pool.take (p : Pool α) : Option α × Pool α :=
  if p.lifoPolls < p.lifoCap then
    match p.lifo with
    | some x => (some x, { p with lifo := none, lifoPolls := p.lifoPolls + 1, taken := p.taken + 1 })
    | none   => p.takeFromRing
  else
    match p.lifo with
    | some x => ({ p with lifo := none, inject := p.inject ++ [x] }).takeFromRing
    | none   => p.takeFromRing

/-- A thief takes one element from the front of a victim's ring. It cannot reach the LIFO slot. -/
def Pool.steal (victim : Pool α) : Option α × Pool α := victim.takeFromRing

/-- A tick: the LIFO allowance refreshes. -/
def Pool.tick (p : Pool α) : Pool α := { p with lifoPolls := 0 }

/-! ### Submitting -/

/-- Submit, with overflow.

If the ring has room, append at the back. Otherwise move **half** the ring to `inject` and append —
half, not all, so the ring keeps the older work and does not immediately refill into another overflow
(`queue.rs:253`). -/
def Pool.submit (p : Pool α) (x : α) : Pool α :=
  if p.ring.length < p.cap then
    { p with ring := p.ring ++ [x], pushed := p.pushed + 1 }
  else
    { p with ring   := p.ring.take (p.ring.length / 2) ++ [x],
             inject := p.inject ++ p.ring.drop (p.ring.length / 2),
             pushed := p.pushed + 1 }

/-! ### What the overflow keeps, and what it evicts

The two halves are not interchangeable, and `queue.rs:295` gives the reason: intake places work in the
*first* half of the ring, so a task found in the *second* half is provably not one just intaken — "at
least not until after we have polled it at least once". That is only true if the *second* half is what
gets evicted, which is what these two examples pin. -/

/-- The ring keeps the older half, plus the new task. -/
example : (({(emptyPool Nat) with cap := 4, ring := [0, 1, 2, 3]}).submit 4).ring = [0, 1, 4] := by
  decide

/-- The newer half is what leaves for `inject`. -/
example : (({(emptyPool Nat) with cap := 4, ring := [0, 1, 2, 3]}).submit 4).inject = [2, 3] := by
  decide

/-! ### The conservation law -/

/-- `take` and `drop` partition a list, at any split point. Stated separately because `omega` treats
`l.length / 2` as an opaque atom and cannot relate it to `l.length` on its own. -/
theorem length_take_add_drop {α : Type} (l : List α) (n : Nat) :
    (l.take n).length + (l.drop n).length = l.length := by
  rw [List.length_take, List.length_drop]
  by_cases h : n ≤ l.length
  · rw [Nat.min_eq_left h]; omega
  · have hle : l.length ≤ n := Nat.le_of_lt (Nat.lt_of_not_le h)
    rw [Nat.min_eq_right hle, Nat.sub_eq_zero_of_le hle]
    omega

theorem takeFromRing_conserves {p : Pool α} (h : p.Consistent) :
    (p.takeFromRing).2.Consistent := by
  unfold Pool.takeFromRing
  cases hr : p.ring with
  | cons x rest =>
    simp_all [Pool.Consistent, Pool.inFlight]
    omega
  | nil =>
    cases hi : p.inject with
    | cons y rest =>
      simp_all [Pool.Consistent, Pool.inFlight]
      omega
    | nil => simpa [Pool.Consistent, Pool.inFlight, hr, hi] using h

theorem take_conserves {p : Pool α} (h : p.Consistent) : (p.take).2.Consistent := by
  unfold Pool.take
  by_cases hp : p.lifoPolls < p.lifoCap
  · simp only [hp, ite_true]
    cases hl : p.lifo with
    | some x =>
      simp_all [Pool.Consistent, Pool.inFlight]
      omega
    | none   => exact takeFromRing_conserves h
  · simp only [hp, ite_false]
    cases hl : p.lifo with
    | some x =>
      refine takeFromRing_conserves ?_
      simp_all [Pool.Consistent, Pool.inFlight]
      omega
    | none => exact takeFromRing_conserves h

theorem steal_conserves {p : Pool α} (h : p.Consistent) : (p.steal).2.Consistent :=
  takeFromRing_conserves h

theorem submit_conserves {p : Pool α} (x : α) (h : p.Consistent) :
    (p.submit x).Consistent := by
  unfold Pool.submit
  by_cases hc : p.ring.length < p.cap
  · simp only [hc, ite_true]
    simp_all [Pool.Consistent, Pool.inFlight]
    omega
  · simp only [hc, ite_false]
    have hsum := length_take_add_drop p.ring (p.ring.length / 2)
    simp only [Pool.Consistent, Pool.inFlight, List.length_append, List.length_singleton] at h ⊢
    omega

theorem tick_conserves {p : Pool α} (h : p.Consistent) : (p.tick).Consistent := h

/-! ### Capacity -/

theorem submit_bounded {p : Pool α} {x : α} (hb : p.Bounded) (hcap : 2 ≤ p.cap) :
    (p.submit x).Bounded := by
  unfold Pool.submit Pool.Bounded
  by_cases hc : p.ring.length < p.cap
  · simp only [hc, ite_true, List.length_append, List.length_singleton]
    omega
  · simp only [hc, ite_false, List.length_append, List.length_singleton]
    have hb' : p.ring.length ≤ p.cap := hb
    have hdiv : p.ring.length / 2 ≤ p.ring.length := Nat.div_le_self _ _
    have htake : (p.ring.take (p.ring.length / 2)).length = p.ring.length / 2 := by
      rw [List.length_take, Nat.min_eq_left hdiv]
    omega

/-! ### No work is stranded -/

/-- The ring-or-inject case on its own, so both the owner's take and a thief's steal can reuse it. -/
theorem takeFromRing_returns_if_present {p : Pool α} (h : p.ring ≠ [] ∨ p.inject ≠ []) :
    (p.takeFromRing).1.isSome := by
  unfold Pool.takeFromRing
  cases hr : p.ring with
  | cons x rest => simp
  | nil =>
    cases hi : p.inject with
    | cons y rest => simp
    | nil => simp [hr, hi] at h

/-- **`take` returns something whenever there is work.**

This is the theorem the flush exists for. Without it, the LIFO allowance could look at a full slot,
decline to take it, find the ring and inject empty, and report `none` — stranding work while
`Consistent` still held. `Consistent` alone does not rule that out; this does. -/
theorem take_returns_if_present {p : Pool α} (h : p.HasWork) : (p.take).1.isSome := by
  unfold Pool.take
  by_cases hp : p.lifoPolls < p.lifoCap
  · simp only [hp, ite_true]
    cases hl : p.lifo with
    | some x => simp
    | none   => exact takeFromRing_returns_if_present (by simpa [Pool.HasWork, hl] using h)
  · simp only [hp, ite_false]
    cases hl : p.lifo with
    | some x => exact takeFromRing_returns_if_present (Or.inr (by simp))
    | none   => exact takeFromRing_returns_if_present (by simpa [Pool.HasWork, hl] using h)

/-- Stealing is the same claim for a thief, and it deliberately cannot see the LIFO slot — so work
held *only* in the slot is not stealable, which is the documented behaviour. The vacuity checks below
show that this is a real restriction and not vacuity. -/
theorem steal_returns_if_ring_or_inject_nonempty {p : Pool α}
    (h : p.ring ≠ [] ∨ p.inject ≠ []) : (p.steal).1.isSome :=
  takeFromRing_returns_if_present h

/-! ### Vacuity checks

Each predicate must be shown to distinguish, or a theorem about it is true of everything and means
nothing. -/

/-- A fresh pool is consistent: nothing submitted, nothing taken. -/
example : (emptyPool Nat).Consistent := by simp [Pool.Consistent, Pool.inFlight, emptyPool]

/-- …and an inconsistent pool exists, so `Consistent` is not true of everything. -/
example : ¬ ({(emptyPool Nat) with pushed := 1}).Consistent := by
  simp [Pool.Consistent, Pool.inFlight, emptyPool]

/-- An empty pool has no work… -/
example : ¬ (emptyPool Nat).HasWork := by simp [Pool.HasWork, emptyPool]

/-- …and a pool holding only a LIFO task has work — which is the case `steal` cannot reach. -/
example : ({(emptyPool Nat) with lifo := some 7}).HasWork := by
  simp [Pool.HasWork, emptyPool]

/-- The control for `steal`'s restriction: work in the LIFO slot alone is genuinely not stealable. -/
example : ({(emptyPool Nat) with lifo := some 7}).steal.1 = none := rfl

/-- The affirmative control for `take`: the owner *can* reach the slot that a thief cannot. -/
example : ({(emptyPool Nat) with lifo := some 7}).take.1 = some 7 := by
  simp [Pool.take, emptyPool]

/-! ### The audit

None of the model's theorems should rest on the bridge axioms — the pool is *about* the primitives, so
a proof that depended on one would be circular. `#print axioms` is the check. -/

#print axioms LeanIn.Model.take_returns_if_present
#print axioms LeanIn.Model.submit_conserves
#print axioms LeanIn.Model.submit_bounded
#print axioms LeanIn.Model.take_conserves

end Model

end LeanIn
