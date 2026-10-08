import LeanIn.Theory.Bridge

/-!
# Controls for representation dependence

`Runs` takes the representation as a parameter, so a witness belongs to one interpretation and cannot be
re-instantiated under another. These controls exist because that was not true of the earlier signature,
where the difference cost a claim about a single mutex becoming a claim about every model lock.

The countermodel is **not a bridge axiom**. It reproduces the superseded shape -- an interpretation that
does not mention `Rep`, with a contract quantifying over every `Rep` -- so that the defect it caused can be
demonstrated rather than described. Nothing here is imported by the library, and none of it names a
runtime operation.
-/

namespace LeanIn

/-- The superseded interpretation: a world pair and an operation, with no representation. -/
opaque OldRuns {α : Type} (t : Tid) (op : BaseIO α) (w : World) (res : α) (w' : World) : Prop

/-- The superseded acquisition contract: it quantified over every representation while the interpretation
named none. -/
axiom old_lock_spec {r : Rep} {m : Std.BaseMutex} {w w' : World} {l : LockId} {t : Tid} :
    IsLock r m l → OldRuns t (Std.BaseMutex.lock m) w () w' → (w'.locks l).owner = some t

/-- **The countermodel.** One acquisition, read at a constant representation, sets *every* model lock's
owner to the caller. This is the derivation that compelled the repair. -/
theorem lock_claim_for_every_index {m : Std.BaseMutex} {w w' : World} {t : Tid}
    (h : OldRuns t (Std.BaseMutex.lock m) w () w') :
    ∀ l : LockId, (w'.locks l).owner = some t := by
  intro l
  let r : Rep := { lockOf := fun _ => l, condOf := fun _ => 0 }
  exact old_lock_spec (rfl : IsLock r m l) h

/-- The superseded broadcast contract, with the same shape. -/
axiom old_notifyAll_spec {r : Rep} {cv : Std.Condvar} {w w' : World} {c : CondvarId} {t : Tid} :
    IsCondvar r cv c → OldRuns t (Std.Condvar.notifyAll cv) w () w' →
    (∀ u, u ∈ (w.condvars c).waiters → u ∉ (w'.condvars c).waiters) ∧
    (∀ u, u ∈ (w'.condvars c).waiters → u ∈ (w.condvars c).waiters)

/-- **The same shape for a broadcast**: one notification empties *every* model condvar. -/
theorem notifyAll_empties_every_condvar {cv : Std.Condvar} {w w' : World} {t : Tid}
    (h : OldRuns t (Std.Condvar.notifyAll cv) w () w') :
    ∀ c : CondvarId, (w'.condvars c).waiters = [] := by
  intro c
  let r : Rep := { lockOf := fun _ => 0, condOf := fun _ => c }
  obtain ⟨hgone, hno⟩ := old_notifyAll_spec (rfl : IsCondvar r cv c) h
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro u hu
  exact (hgone u (hno u hu)) hu

/-- **The guarded form: the only shape now available.** A witness at representation `r` supports a claim
about the index `r` names, and reaching a second index needs a second witness. This is the regression
guard as much as a demonstration -- remove `r` from `Runs` and this statement stops typechecking, which is
what makes the parameter structural rather than decorative. -/
theorem lock_sets_only_the_index_it_names {r : Rep} {m : Std.BaseMutex} {w w' : World} {l : LockId}
    {t : Tid} (hL : IsLock r m l) (h : Runs r t (Std.BaseMutex.lock m) w () w') :
    (w'.locks l).owner = some t :=
  (lock_spec hL h).1

/-- Entry point. The proofs are checked when this module compiles; the report names what they establish and
what the countermodel is for. -/
def bridgeControlsMain : IO UInt32 := do
  IO.println "representation dependence controls"
  IO.println "  countermodel: under the superseded shape, one acquisition set every model lock's owner,"
  IO.println "                and one broadcast emptied every model condvar (both proved above)"
  IO.println "  guarded form: a witness at one representation supports one index, and no other"
  IO.println "  the parameter is structural: removing it from `Runs` breaks the guarded form's types"
  return 0

#print axioms LeanIn.lock_sets_only_the_index_it_names
#print axioms LeanIn.lock_claim_for_every_index

end LeanIn
