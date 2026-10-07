import Std

-- `toList` is the only declaration that needs `Inhabited`; the laws about `WF` and the operations do
-- not, so the section variable is unused in those. Kept as a section variable for readability.
set_option linter.unusedSectionVars false

/-!
# The ring buffer

The container the pool model describes (D12). `Pool.ring : List α` is the *specification*; this is the
implementation, and `Ring.toList` is the ghost view that ties the two together — so every proof
downstream of here is about a list and never about an index.

## Shape

Fixed store, the index of the oldest live element, and a live count. `push` writes at
`(head + size) % cap` and `pop` clears `head % cap` and advances, so neither moves any other element —
which is the whole point, and the reason `List` could not be the container.

`Ring.WF` carries three conjuncts, and the third is the interesting one: the live range is **dense**,
so `toList` reads real elements rather than falling back to a default. `pop_isSome` is what makes that
conjunct load-bearing — without it, a `pop` on a non-empty ring could return `none`.

## Where the arithmetic lives

In `slot_ne`, and nowhere else. It says distinct live indices occupy distinct slots, so the ghost view
reads distinct elements and a write at the free position cannot disturb a live one. Nothing below the
ghost view ever sees `%`.

**How the arithmetic is done.** `omega` handles `%` only after it is eliminated, so `slot_ne` normalises
first (`Nat.mod_add_mod`) and then splits on whether each argument is below or above `cap`. The one
non-obvious step: the `≥ cap` branch must carry its **side condition** out of the split. A bare
`m % cap = m - cap` is useless to `omega`, because `Nat` subtraction saturates — `m - cap` is `0` when
`m < cap`, so the equation alone admits `m = cap = 0`... not a contradiction. Carrying `cap ≤ m`
alongside is what makes it refutable.
-/

namespace LeanIn

/-- A bounded FIFO ring buffer. -/
structure Ring (α : Type) (cap : Nat) where
  /-- Backing store, in physical order. Slots outside the live range are `none`. -/
  slots : List (Option α) := []
  /-- Physical index of the oldest live element. -/
  head  : Nat := 0
  /-- Number of live elements. -/
  size  : Nat := 0
deriving Inhabited, Repr

/-- The all-empty ring, written out so examples reduce. -/
def emptyRing (α : Type) (cap : Nat) : Ring α cap := { slots := [], head := 0, size := 0 }

variable {α : Type} [Inhabited α]

/-- **The ghost view.** The live elements, oldest first. All reasoning happens here. -/
def Ring.toList (r : Ring α cap) : List α :=
  (List.range r.size).map fun i => ((r.slots[(r.head + i) % cap]?).join).getD default

/-- Well-formedness.

`dense` says the live slots hold **elements**, not merely that the slots exist — note the `join`,
without which a slot containing `none` would satisfy the conjunct while `toList` quietly fell back to
a default. -/
def Ring.WF (r : Ring α cap) : Prop :=
  r.slots.length = cap ∧ r.size ≤ cap ∧
  ∀ i, i < r.size → ((r.slots[(r.head + i) % cap]?).join).isSome

/-- Push at the free end. No element moves. -/
def Ring.push (r : Ring α cap) (x : α) : Ring α cap :=
  { r with slots := r.slots.set ((r.head + r.size) % cap) (some x), size := r.size + 1 }

/-- Pop the oldest. No element moves. -/
def Ring.pop (r : Ring α cap) : Option α × Ring α cap :=
  if 0 < r.size then
    match r.slots[r.head % cap]? with
    | some (some x) =>
      (some x, { r with slots := r.slots.set (r.head % cap) none,
                        head  := (r.head + 1) % cap,
                        size  := r.size - 1 })
    | _ => (none, r)
  else (none, r)

/-! ### The one modular lemma -/

/-- **Distinct live indices occupy distinct slots.**

Everything modular is here. `j < cap` rather than `j < size` because `push` compares the *free*
position `size` against the live indices. -/
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

/-! ### The laws tying the container to the spec -/

theorem push_toList (r : Ring α cap) (x : α) (hw : r.WF) (hroom : r.size < cap) :
    (r.push x).toList = r.toList ++ [x] := by
  have hcap : 0 < cap := Nat.lt_of_le_of_lt (Nat.zero_le _) hroom
  unfold Ring.push Ring.toList
  rw [List.range_succ, List.map_append, List.map_cons, List.map_nil]
  congr 1
  · apply List.map_congr_left
    intro i hi
    simp only [List.mem_range] at hi
    have hne : (r.head + i) % cap ≠ (r.head + r.size) % cap := slot_ne hcap hi hroom
    simp only [List.getElem?_set_ne hne.symm]
  · have hw' : (r.head + r.size) % cap < r.slots.length := by
      rw [hw.1]; exact Nat.mod_lt _ hcap
    simp [List.getElem?_set_self hw']

/-- **Density does work.** A non-empty ring can always be popped — exactly the `dense` conjunct of
`WF`, and false without it: a slot holding `none` would satisfy the weaker form. -/
theorem pop_isSome (r : Ring α cap) (hw : r.WF) (hpos : 0 < r.size) : (r.pop).1.isSome := by
  have hden := hw.2.2 0 hpos
  simp only [Nat.add_zero] at hden
  unfold Ring.pop
  rw [ite_eq_left hpos]
  cases hm : r.slots[r.head % cap]? with
  | none => rw [hm] at hden; simp at hden
  | some v =>
    cases v with
    | none => rw [hm] at hden; simp at hden
    | some x => simp

-- Some arguments of the `simp only` below are redundant. They are kept because trimming them changes
-- what `simp` rewrites and breaks the proof, so the warning is silenced here rather than left as noise.
set_option linter.unusedSimpArgs false in
theorem pop_toList (r : Ring α cap) (hw : r.WF) (hpos : 0 < r.size) :
    ∃ x, (r.pop).1 = some x ∧ r.toList = x :: (r.pop).2.toList := by
  have hcap : 0 < cap := Nat.lt_of_lt_of_le hpos hw.2.1
  have hden := hw.2.2 0 hpos
  simp only [Nat.add_zero] at hden
  obtain ⟨k, hk⟩ : ∃ k, r.size = k + 1 := ⟨r.size - 1, by omega⟩
  unfold Ring.pop
  rw [ite_eq_left hpos]
  cases hm : r.slots[r.head % cap]? with
  | none => rw [hm] at hden; simp at hden
  | some v =>
    cases v with
    | none => rw [hm] at hden; simp at hden
    | some x =>
      refine ⟨x, rfl, ?_⟩
      unfold Ring.toList
      simp only [hm, hk, Option.join, Option.getD_some, Nat.add_assoc]
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      · simp [hm]
      · apply List.map_congr_left
        intro i hi
        simp only [List.mem_range] at hi
        have hle : r.size ≤ cap := hw.2.1
        have hi2 : i + 1 < cap := by omega
        have hne : (r.head + 0) % cap ≠ (r.head + (i + 1)) % cap :=
          slot_ne hcap (by omega) hi2
        simp only [Nat.add_zero] at hne
        have hshift : ((r.head + 1) % cap + i) % cap = (r.head + (i + 1)) % cap := by
          rw [Nat.mod_add_mod]; congr 1; omega
        simp only [Function.comp_apply, hshift, List.getElem?_set_ne hne]

/-! ### The invariant is preserved

Without these the laws above would be one-shot: a container that does not preserve its own
well-formedness is not a container. -/

theorem push_wf (r : Ring α cap) (x : α) (hw : r.WF) (hroom : r.size < cap) :
    (r.push x).WF := by
  have hcap : 0 < cap := Nat.lt_of_le_of_lt (Nat.zero_le _) hroom
  refine ⟨?_, ?_, ?_⟩
  · simp [Ring.push, List.length_set, hw.1]
  · simp only [Ring.push]; omega
  · intro i hi
    simp only [Ring.push] at hi ⊢
    by_cases hic : i < r.size
    · have hne : (r.head + i) % cap ≠ (r.head + r.size) % cap := slot_ne hcap hic hroom
      simp only [List.getElem?_set_ne hne.symm]
      exact hw.2.2 i hic
    · have hie : i = r.size := by omega
      subst hie
      have hw' : (r.head + r.size) % cap < r.slots.length := by
        rw [hw.1]; exact Nat.mod_lt _ hcap
      simp [List.getElem?_set_self hw']

theorem pop_wf (r : Ring α cap) (hw : r.WF) (hpos : 0 < r.size) : (r.pop).2.WF := by
  have hcap : 0 < cap := Nat.lt_of_lt_of_le hpos hw.2.1
  have hden := hw.2.2 0 hpos
  simp only [Nat.add_zero] at hden
  unfold Ring.pop
  rw [ite_eq_left hpos]
  cases hm : r.slots[r.head % cap]? with
  | none => rw [hm] at hden; simp at hden
  | some v =>
    cases v with
    | none => rw [hm] at hden; simp at hden
    | some x =>
      have hle : r.size ≤ cap := hw.2.1
      show (r.slots.set (r.head % cap) none).length = cap ∧ (r.size - 1 ≤ cap) ∧
           ∀ i, i < r.size - 1 →
             ((r.slots.set (r.head % cap) none)[((r.head + 1) % cap + i) % cap]?).join.isSome
      refine ⟨?_, ?_, ?_⟩
      · simp [List.length_set, hw.1]
      · omega
      · intro i hi
        have hi2 : i + 1 < cap := by omega
        have hne : (r.head + 0) % cap ≠ (r.head + (i + 1)) % cap :=
          slot_ne hcap (by omega) hi2
        simp only [Nat.add_zero] at hne
        have hshift : ((r.head + 1) % cap + i) % cap = (r.head + (i + 1)) % cap := by
          rw [Nat.mod_add_mod]; congr 1; omega
        rw [hshift]
        simp only [List.getElem?_set_ne hne]
        exact hw.2.2 (i + 1) (by omega)

/-! ### The audit

**Outstanding, and recorded rather than hidden:** the vacuity checks for `Ring` are not written.
`emptyRing` witnesses that `WF` is inhabited and a ring with `size > cap` witnesses that it
distinguishes, but three `example`s attempting exactly that were withdrawn — `simp`'s handling of the
`emptyRing` projection fought harder than the theorems did. Tracked in `PLAN.md` M2b.

The laws themselves are checked:

`#print axioms` reports what each rests on. -/

#print axioms LeanIn.slot_ne
#print axioms LeanIn.push_toList
#print axioms LeanIn.pop_toList
#print axioms LeanIn.push_wf
#print axioms LeanIn.pop_wf

end LeanIn
