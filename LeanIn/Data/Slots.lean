module

public import Std


public section
-- `toList` is the only declaration that needs `Inhabited`; the index arithmetic and `slot_ne` do not, so the
-- section variable is unused in those. Kept as a section variable for readability.
set_option linter.unusedSectionVars false

/-!
# The ring's store

The ring keeps its live range in an `Array` of slots with the index of the oldest live element: `Array.set`
modifies in place when the array is uniquely referenced, whereas `List.set` copies a prefix. The store is a fixed
`cap` slots and its free position wraps modulo `cap`. `LeanIn.Data.Deque` used to share it and no longer does: an
unbounded queue held in a shared cell cannot afford a store that a write copies (see that file).

So the store is here: the three fields, the ghost view parameterised by the index function, the density
predicate a view needs, and `slot_ne`, the one modular lemma that keeps `%` out of everything below it. A
container supplies its own index function and its own capacity obligation; nothing below the view ever sees
`%` or an index at all.
-/

namespace LeanIn

/-- The store: an array of slots, the index of the oldest live element, and the live count.

`head` is meaningful only through a container's index function: the ring wraps it modulo `cap`. The store itself
does not care. -/
structure Slots (α : Type) where
  /-- Backing store, in physical order. Slots outside the live range are `none`. -/
  slots : Array (Option α) := #[]
  /-- Index of the oldest live element, under the container's own index function. -/
  head  : Nat := 0
  /-- Number of live elements. -/
  size  : Nat := 0
deriving Inhabited, Repr

variable {α : Type} [Inhabited α]

/-- **The ghost view**, under an index function: the live elements, oldest first. All reasoning about a
container happens here, through the `List` its index function reads. -/
@[expose] def Slots.toList (s : Slots α) (idx : Nat → Nat) : List α :=
  (List.range s.size).map fun i => ((s.slots[idx i]?).join).getD default

/-- **The ghost view has as many elements as the store reports.** Not conditional on density: the view maps
over `List.range s.size`, so a slot holding `none` contributes its `default` rather than disappearing —
which is why density is needed for *element* reasoning and is not needed here. -/
theorem Slots.toList_length (s : Slots α) (idx : Nat → Nat) : (s.toList idx).length = s.size := by
  simp [Slots.toList]

/-- **Density**: every index the view reads holds an element rather than an empty slot. -/
@[expose] def Slots.Dense (s : Slots α) (idx : Nat → Nat) : Prop :=
  ∀ i, i < s.size → ((s.slots[idx i]?).join).isSome

/-- Write one slot, leaving the live range alone. The one store mutation both containers perform; a
container updates `head` and `size` itself, since those are what it disagrees with the other about. -/
def Slots.setSlot (s : Slots α) (i : Nat) (v : Option α) : Slots α :=
  { s with slots := s.slots.setIfInBounds i v }

/-! ### The one modular lemma -/

/-- **Distinct live indices occupy distinct slots.**

Everything modular is here. `j < cap` rather than `j < size` because a push compares the *free* position
`size` against the live indices. The ring's index function is the only caller.

**How the arithmetic is done.** `omega` handles `%` only after it is eliminated, so this normalises first
(`Nat.mod_add_mod`) and then splits on whether each argument is below or above `cap`. The one non-obvious
step: the `≥ cap` branch must carry its **side condition** out of the split. A bare `m % cap = m - cap` is
useless to `omega`, because `Nat` subtraction saturates — `m - cap` is `0` when `m < cap`, so the equation
alone admits `m = cap = 0`... not a contradiction. Carrying `cap ≤ m` alongside is what makes it refutable. -/
theorem slot_ne {cap head i j : Nat} (hcap : 0 < cap) (hij : i < j) (hj : j < cap) :
    (head + i) % cap ≠ (head + j) % cap := by
  intro h
  have h0 : head % cap < cap := Nat.mod_lt _ hcap
  have h' : (head % cap + i) % cap = (head % cap + j) % cap := by
    rw [Nat.mod_add_mod, Nat.mod_add_mod]; exact h
  have key : ∀ m, m < 2 * cap → m % cap = m ∨ (cap ≤ m ∧ m % cap = m - cap) := by
    intro m hm
    by_cases hc : m < cap
    · exact Or.inl (Nat.mod_eq_of_lt hc)
    · refine Or.inr ⟨Nat.not_lt.mp hc, ?_⟩
      have hsplit : m = (m - cap) + 1 * cap := by omega
      rw [hsplit, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      omega
  have hi2 : head % cap + i < 2 * cap := by omega
  have hj2 : head % cap + j < 2 * cap := by omega
  rcases key _ hi2 with h1 | ⟨h1ge, h1⟩
  · rcases key _ hj2 with h2 | ⟨h2ge, h2⟩
    · rw [h1, h2] at h'; omega
    · rw [h1, h2] at h'; omega
  · rcases key _ hj2 with h2 | ⟨h2ge, h2⟩
    · rw [h1, h2] at h'; omega
    · rw [h1, h2] at h'; omega

/-! ### The audit

`#print axioms` reports what the store's reasoning rests on. -/

#print axioms LeanIn.slot_ne

end LeanIn

end
