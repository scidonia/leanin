module

public import Std


public section

/-!
# The deque: an unbounded queue that never writes an existing object

The inject is a FIFO that is appended at the back and taken from the front. It lives in a `Std.Mutex`, and that
decides the container. A value stored in a cell another thread can reach is marked multi-threaded, a marked object
is never exclusive, and so **every write to an `Array` held there copies the whole array**, whatever the
transaction does about its own references. A store-based queue is O(depth) per operation in exactly the state a
running executor is in (`docs/PERFORMANCE.md`, "The inject's depth cliff").

So nothing here is written in place. A push conses one cell onto `back`, and marking it stops at the tail, which
is already marked. A pop reads the head of `front`. When `front` runs out, `back` is reversed into it, and that is
the only step that is not constant: each element takes it once, so the walk is O(1) amortised, and it is paid in
one pop, under the lock, rather than spread out. `Task/Sync.lean`'s channel keeps its buffer the same way.

`Deque.toList` is the ghost view and the whole specification: a push appends to the view's back, a pop removes
from its front, and the *append lemma* below is what carries the implementation to the model's `inject : List α`,
in the D12 container-and-ghost-view pattern. Nothing here can state the cost above, because sharing is a property
of the runtime's reference counts and not of the values: `tests/queue-scaling.sh` is what holds it.
-/

namespace LeanIn

/-- An unbounded FIFO queue over two lists: pushed onto `back`, popped off `front`. -/
structure Deque (α : Type) where
  /-- The read side, oldest first. -/
  front : List α := []
  /-- The write side, newest first. -/
  back  : List α := []
  /-- Number of live elements, kept so an emptiness test under the lock does not walk anything. -/
  size  : Nat := 0
deriving Inhabited, Repr

variable {α : Type}

/-- **The ghost view.** The live elements, oldest first. -/
@[expose] def Deque.toList (d : Deque α) : List α :=
  d.front ++ d.back.reverse

/-- Well-formedness: the count is the two sides' lengths. -/
@[expose] def Deque.WF (d : Deque α) : Prop :=
  d.size = d.front.length + d.back.length

/-- The empty deque. -/
def Deque.empty : Deque α := {}

/-- A fresh deque is well-formed. -/
theorem Deque.empty_wf : (Deque.empty (α := α)).WF := by
  simp [Deque.empty, Deque.WF]

/-- **The view has as many elements as the deque reports.** -/
theorem Deque.toList_length (d : Deque α) (hw : d.WF) : d.toList.length = d.size := by
  simp only [Deque.toList, List.length_append, List.length_reverse]
  exact hw.symm

/-- **The count is an emptiness test.** The park predicate reads `size` under the lock and never the lists, so a
refused park and an empty view have to be the same fact. -/
theorem Deque.size_eq_zero_iff (d : Deque α) (hw : d.WF) : d.size = 0 ↔ d.toList = [] := by
  rw [← Deque.toList_length d hw]
  exact List.length_eq_zero_iff

/-! ### The operations -/

/-- **Push at the back.** One cell, and nothing existing is written. -/
@[expose] def Deque.push (d : Deque α) (x : α) : Deque α :=
  { d with back := x :: d.back, size := d.size + 1 }

/-- **Pop from the front**, reversing the write side into the read side when the read side has run out. -/
@[expose] def Deque.pop (d : Deque α) : Option α × Deque α :=
  match d.front with
  | x :: rest => (some x, { d with front := rest, size := d.size - 1 })
  | [] =>
    match d.back.reverse with
    | x :: rest => (some x, { front := rest, back := [], size := d.size - 1 })
    | [] => (none, d)

/-! ### The laws tying the container to the spec -/

/-- **A push appends to the view.** The append lemma the model's `inject` refinement reads. -/
theorem Deque.push_toList (d : Deque α) (x : α) : (d.push x).toList = d.toList ++ [x] := by
  simp [Deque.push, Deque.toList]

/-- **A push keeps well-formedness.** -/
theorem Deque.push_wf (d : Deque α) (x : α) (hw : d.WF) : (d.push x).WF := by
  simp only [Deque.WF, Deque.push, List.length_cons] at hw ⊢
  omega

/-- What a pop does, read off the view: a non-empty deque hands back its head and keeps the rest, and the result
is well-formed. The three laws below are this one, split; it is one statement because the two arms of `pop` have
to be cased together. -/
private theorem Deque.pop_spec (d : Deque α) (hw : d.WF) (hpos : 0 < d.size) :
    ∃ x, (d.pop).1 = some x ∧ d.toList = x :: (d.pop).2.toList ∧ (d.pop).2.WF := by
  unfold Deque.pop Deque.WF Deque.toList at *
  cases hf : d.front with
  | cons x rest =>
    rw [hf] at hw
    simp only [List.length_cons] at hw
    exact ⟨x, rfl, by simp, by simp only; omega⟩
  | nil =>
    rw [hf] at hw
    simp only [List.length_nil] at hw
    cases hr : d.back.reverse with
    | cons x rest =>
      have hlen := congrArg List.length hr
      simp only [List.length_reverse, List.length_cons] at hlen
      exact ⟨x, rfl, by simp, by simp only [List.length_nil]; omega⟩
    | nil =>
      have hlen := congrArg List.length hr
      simp only [List.length_reverse, List.length_nil] at hlen
      omega

/-- **A pop removes from the front of the view.** -/
theorem Deque.pop_toList (d : Deque α) (hw : d.WF) (hpos : 0 < d.size) :
    ∃ x, (d.pop).1 = some x ∧ d.toList = x :: (d.pop).2.toList :=
  let ⟨x, hx, hv, _⟩ := Deque.pop_spec d hw hpos
  ⟨x, hx, hv⟩

/-- **A pop keeps well-formedness.** -/
theorem Deque.pop_wf (d : Deque α) (hw : d.WF) (hpos : 0 < d.size) : (d.pop).2.WF :=
  let ⟨_, _, _, h⟩ := Deque.pop_spec d hw hpos
  h

/-- **A non-empty deque can always be popped.** -/
theorem Deque.pop_isSome (d : Deque α) (hw : d.WF) (hpos : 0 < d.size) : (d.pop).1.isSome :=
  let ⟨x, hx, _, _⟩ := Deque.pop_spec d hw hpos
  hx ▸ rfl

/-- A pop that returned an element had one. -/
theorem Deque.pop_isSome_size {d : Deque α} (hw : d.WF) (h : (d.pop).1.isSome) : 0 < d.size := by
  refine Nat.pos_of_ne_zero fun h0 => ?_
  have hf : d.front = [] := by
    apply List.eq_nil_of_length_eq_zero
    simp only [Deque.WF] at hw
    omega
  have hb : d.back.reverse = [] := by
    apply List.eq_nil_of_length_eq_zero
    simp only [Deque.WF] at hw
    simp only [List.length_reverse]
    omega
  simp [Deque.pop, hf, hb] at h

/-- Popping leaves one fewer element. -/
theorem Deque.pop_size (d : Deque α) (hw : d.WF) (hpos : 0 < d.size) : (d.pop).2.size + 1 = d.size := by
  obtain ⟨x, _, hlist, hw'⟩ := Deque.pop_spec d hw hpos
  have h := congrArg List.length hlist
  simp only [List.length_cons] at h
  rw [Deque.toList_length d hw, Deque.toList_length _ hw'] at h
  omega

/-! ### Vacuity and the audit

The predicates must be shown to distinguish, or the laws above could be true of nothing. -/

/-- A fresh deque is well-formed. -/
example : (Deque.empty (α := Nat)).WF := Deque.empty_wf

/-- The empty deque's view is empty. -/
example : (Deque.empty (α := Nat)).toList = [] := rfl

/-- …and a deque whose count disagrees with its lists is **not** well-formed, so `WF` is not true of
everything. -/
example : ¬ (Deque.WF ({ front := [1], back := [], size := 2 } : Deque Nat)) := by
  simp [Deque.WF]

/-- The laws compose: a push is visible in the view, and the deque it built is well-formed. -/
example : ((Deque.empty (α := Nat)).push 7).toList = [7] := by
  rw [Deque.push_toList]; rfl

example : ((Deque.empty (α := Nat)).push 7).WF := Deque.push_wf _ _ Deque.empty_wf

/-- The reversal is reached through real pushes and keeps FIFO order: two pushes land on the write side, the first
pop reverses them and returns the older, and a later push waits behind what the reversal moved. -/
example : (((Deque.empty (α := Nat)).push 1 |>.push 2).pop.1) = some 1 := by decide

example : ((((Deque.empty (α := Nat)).push 1 |>.push 2).pop.2.push 3).toList) = [2, 3] := by decide

-- The audit: the deque's reasoning is Lean's own.
#print axioms LeanIn.Deque.push_toList
#print axioms LeanIn.Deque.pop_toList
#print axioms LeanIn.Deque.push_wf
#print axioms LeanIn.Deque.pop_wf
#print axioms LeanIn.Deque.size_eq_zero_iff

end LeanIn

end
