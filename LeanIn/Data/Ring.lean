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

A **fixed-size `Array`** of slots, the index of the oldest live element, and a live count. `push` writes
at `(head + size) % cap` and `pop` clears `head % cap` and advances, so neither moves any other element.

The store is an `Array` and not a `List` because that is the whole point of a ring: `Array.set`
modifies in place when the array is uniquely referenced, whereas `List.set` copies a prefix. The `List`
in this file appears **only** in `Ring.toList`, the ghost view, where its algebraic lemmas make the
proofs short — the split Lean's own containers use, e.g. `Std.DHashMap` (Array implementation, `List`
model, laws in a separate file).

`push` and `pop` use `Array.setIfInBounds` rather than `Array.set`: the latter demands a bound proof,
and the operations should be total and independent of `WF`. The bounds are available wherever a law
needs them, which is where the `_of_lt` lemmas below come in.

`Ring.WF` carries three conjuncts, and the third is the interesting one: the live range is **dense**, so
`toList` reads real elements rather than falling back to a default. `pop_isSome` is what makes that
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
  slots : Array (Option α) := #[]
  /-- Physical index of the oldest live element. -/
  head  : Nat := 0
  /-- Number of live elements. -/
  size  : Nat := 0
deriving Inhabited, Repr

/-- The all-empty ring: a store of `cap` empty slots. Written out so examples reduce — and note that
`slots` must have size `cap`, which the vacuity checks below are what caught. -/
def emptyRing (α : Type) (cap : Nat) : Ring α cap :=
  { slots := Array.replicate cap none, head := 0, size := 0 }

variable {α : Type} [Inhabited α]

/-- **The ghost view.** The live elements, oldest first. All reasoning happens here. -/
def Ring.toList (r : Ring α cap) : List α :=
  (List.range r.size).map fun i => ((r.slots[(r.head + i) % cap]?).join).getD default

/-- Well-formedness.

`dense` says the live slots hold **elements**, not merely that the slots exist — note the `join`,
without which a slot containing `none` would satisfy the conjunct while `toList` quietly fell back to
a default. -/
def Ring.WF (r : Ring α cap) : Prop :=
  r.slots.size = cap ∧ r.size ≤ cap ∧
  ∀ i, i < r.size → ((r.slots[(r.head + i) % cap]?).join).isSome

/-- Push at the free end. No element moves. -/
def Ring.push (r : Ring α cap) (x : α) : Ring α cap :=
  { r with slots := r.slots.setIfInBounds ((r.head + r.size) % cap) (some x), size := r.size + 1 }

/-- Pop the oldest. No element moves. -/
def Ring.pop (r : Ring α cap) : Option α × Ring α cap :=
  if 0 < r.size then
    match r.slots[r.head % cap]? with
    | some (some x) =>
      (some x, { r with slots := r.slots.setIfInBounds (r.head % cap) none,
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

/-- A fresh ring is well-formed: `cap` empty slots and nothing live. -/
theorem emptyRing_wf (cap : Nat) : (emptyRing α cap).WF := by
  refine ⟨by simp [emptyRing], by simp [emptyRing], ?_⟩
  intro i hi
  exact (Nat.not_lt_zero i hi).elim

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
    simp only [Array.getElem?_setIfInBounds_ne hne.symm]
  · have hw' : (r.head + r.size) % cap < r.slots.size := by
      rw [hw.1]; exact Nat.mod_lt _ hcap
    simp [Array.getElem?_setIfInBounds_self_of_lt hw']

/-- **The ghost view has as many elements as the ring reports.** Not conditional on `WF`: `toList` maps
over `List.range r.size`, so a slot holding `none` contributes its `default` rather than disappearing —
which is why `dense` is needed for *element* reasoning and is not needed here. -/
theorem toList_length (r : Ring α cap) : r.toList.length = r.size := by
  simp [Ring.toList]

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
        simp only [Function.comp_apply, hshift, Array.getElem?_setIfInBounds_ne hne]

/-! ### The invariant is preserved

Without these the laws above would be one-shot: a container that does not preserve its own
well-formedness is not a container. -/

theorem push_wf (r : Ring α cap) (x : α) (hw : r.WF) (hroom : r.size < cap) :
    (r.push x).WF := by
  have hcap : 0 < cap := Nat.lt_of_le_of_lt (Nat.zero_le _) hroom
  refine ⟨?_, ?_, ?_⟩
  · simp [Ring.push, hw.1]
  · simp only [Ring.push]; omega
  · intro i hi
    simp only [Ring.push] at hi ⊢
    by_cases hic : i < r.size
    · have hne : (r.head + i) % cap ≠ (r.head + r.size) % cap := slot_ne hcap hic hroom
      simp only [Array.getElem?_setIfInBounds_ne hne.symm]
      exact hw.2.2 i hic
    · have hie : i = r.size := by omega
      subst hie
      have hw' : (r.head + r.size) % cap < r.slots.size := by
        rw [hw.1]; exact Nat.mod_lt _ hcap
      simp [Array.getElem?_setIfInBounds_self_of_lt hw']

/-- **Popping leaves one fewer element.** The companion to `pop_toList` for reasoning about counts rather
than order: `pop_toList` gives the sequence, `toList_length` turns it into arithmetic, and this is what the
pool's `take` needs to say that it holds one fewer item afterwards. -/
theorem pop_size (r : Ring α cap) (hw : r.WF) (hpos : 0 < r.size) : (r.pop).2.size + 1 = r.size := by
  obtain ⟨x, _, hlist⟩ := pop_toList r hw hpos
  have h := congrArg List.length hlist
  simp only [List.length_cons] at h
  rw [toList_length, toList_length] at h
  omega

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
      show (r.slots.setIfInBounds (r.head % cap) none).size = cap ∧ (r.size - 1 ≤ cap) ∧
           ∀ i, i < r.size - 1 →
             ((r.slots.setIfInBounds (r.head % cap) none)[((r.head + 1) % cap + i) % cap]?).join.isSome
      refine ⟨?_, ?_, ?_⟩
      · simp [hw.1]
      · omega
      · intro i hi
        have hi2 : i + 1 < cap := by omega
        have hne : (r.head + 0) % cap ≠ (r.head + (i + 1)) % cap :=
          slot_ne hcap (by omega) hi2
        simp only [Nat.add_zero] at hne
        have hshift : ((r.head + 1) % cap + i) % cap = (r.head + (i + 1)) % cap := by
          rw [Nat.mod_add_mod]; congr 1; omega
        rw [hshift]
        simp only [Array.getElem?_setIfInBounds_ne hne]
        exact hw.2.2 (i + 1) (by omega)

/-! ### Shedding from the back, by index

Tokio's `push_overflow` removes the newer half of a full queue by **claiming it with indices** and copying those
tasks out, with no read-out and no refill (`queue.rs`, "Add back the first half of tasks"). The same move is
available here and is cheaper still, because `WF` constrains only the live range: a slot outside `[head, head +
size)` is never read by `toList`, and `push` recycles it in order as the ring wraps. So shedding the back of the
live range is **one assignment to `size`** — nothing is copied, shifted or re-filled, and the values that leave
are read exactly once by whoever needs them. -/

/-- **Keep the first `k` live elements and shed the rest.** The index trick: the shed elements leave by moving
the live count, so only the caller's read of what it still holds costs anything.

`min k r.size` rather than `k`, so a caller cannot demand more than is there. -/
def Ring.keepFirst (r : Ring α cap) (k : Nat) : Ring α cap :=
  { r with size := min k r.size }

/-- `map` commutes with `take`, in the direction the next lemma needs. Proved here rather than cited: the core
lemma for this has different names across versions, and it is four cases. -/
theorem map_take {β : Type} (f : Nat → β) : ∀ (l : List Nat) (n : Nat),
    (l.map f).take n = (l.take n).map f
  | [], 0 => rfl
  | [], _ + 1 => rfl
  | _ :: _, 0 => rfl
  | a :: l, n + 1 => by
    show f a :: (l.map f).take n = f a :: (l.take n).map f
    rw [map_take f l n]

/-- **Shedding from the back does not disturb the front.** The kept ring's view is the first `min k size` of the
old view — the split the specification states as `take`. -/
theorem keepFirst_toList (r : Ring α cap) (k : Nat) :
    (r.keepFirst k).toList = r.toList.take (min k r.size) := by
  unfold Ring.keepFirst Ring.toList
  simp only [map_take, List.take_range, Nat.min_assoc, Nat.min_self]

/-- Shedding keeps well-formedness: the live range is a prefix of what it was. -/
theorem keepFirst_wf (r : Ring α cap) (k : Nat) (hw : r.WF) : (r.keepFirst k).WF := by
  have hle : r.size ≤ cap := hw.2.1
  refine ⟨hw.1, by simp only [Ring.keepFirst]; omega, ?_⟩
  intro i hi
  simp only [Ring.keepFirst] at hi
  exact hw.2.2 i (by omega)

/-- A pop that returned an element had one: the `none` arms only run on an empty ring. -/
theorem pop_isSome_size {r : Ring α cap} (h : (r.pop).1.isSome) : 0 < r.size := by
  unfold Ring.pop at h
  split at h
  · assumption
  · simp at h

/-! ### Vacuity and the audit

`WF` must be shown to **distinguish**, or the laws above could be true of nothing. The checks below
use defeq coercion rather than `simp`: `(emptyRing Nat 4).size` reduces to `0` definitionally, but it
is not a `simp` target, which is what defeated three earlier attempts. -/

/-- A fresh ring is well-formed. -/
example : (emptyRing Nat 4).WF := emptyRing_wf 4

/-- …and a ring whose live count exceeds its capacity is **not**, so `WF` is not true of everything. -/
example : ¬ (Ring.WF (α := Nat) (cap := 4) ⟨Array.replicate 4 none, 0, 5⟩) := by
  intro h
  have hle := h.2.1
  have h5 : (5 : Nat) ≤ 4 := hle
  omega

/-- The laws compose: a push preserves `WF`, and a pop of it can always proceed. -/
example : (Ring.pop (Ring.push (emptyRing Nat 4) 7)).1.isSome := by
  have hw : (emptyRing Nat 4).WF := by
    refine ⟨by simp [emptyRing], by simp [emptyRing], ?_⟩
    intro i hi
    exact (Nat.not_lt_zero i hi).elim
  have hroom : (emptyRing Nat 4).size < 4 := by simp [emptyRing]
  exact pop_isSome _ (push_wf _ _ hw hroom) (by simp [Ring.push, emptyRing])

/-! ### The audit

`#print axioms` reports what each law rests on. -/

#print axioms LeanIn.slot_ne
#print axioms LeanIn.push_toList
#print axioms LeanIn.pop_toList
#print axioms LeanIn.push_wf
#print axioms LeanIn.pop_wf

end LeanIn
