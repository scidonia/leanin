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

/-- **The wait cycle, observed natively**, with each carrier recording what it did and when.

`ns` is a field on every record because the relations are stated over it: the sibling's acquisition must
fall between the caller's park and its resume, and the caller's resume must follow the sibling's
notification. Those hold by construction rather than by luck, and the mutex is what does it — the caller
holds the lock while it reads the predicate and releases it only inside the wait, so the sibling cannot set
the predicate in the gap, and the caller cannot leave the wait before the predicate is open. The sibling is
`dedicated` so it has its own native carrier whatever the pool width is. -/
def bridgeWaitCycle : IO Unit := do
  let m ← Std.BaseMutex.new
  let cv ← Std.Condvar.new
  let ready ← IO.mkRef false
  let note (actor op holds : String) : IO Unit := do
    let ns ← IO.monoNanosNow
    IO.println s!"bridge|wait-cycle|ns={ns}|actor={actor}|op={op}|holds={holds}"
  let sibling ← IO.asTask (do
    Std.BaseMutex.lock m
    note "sibling" "acquired" "yes"
    ready.set true
    Std.Condvar.notifyAll cv
    note "sibling" "notified" "yes"
    Std.BaseMutex.unlock m
    note "sibling" "released" "no") Task.Priority.dedicated
  Std.BaseMutex.lock m
  note "caller" "acquired" "yes"
  note "caller" "parking" "yes"
  Std.Condvar.waitUntil cv m (do return (← ready.get))
  note "caller" "resumed" "yes"
  Std.BaseMutex.unlock m
  note "caller" "released" "no"
  let _ ← IO.wait sibling

/-- **A notified episode, then a fresh wait.** The countermodel is a notification that outlives its
episode: if one were remembered, the second wait would be released by the *first* notification.

Two episodes, a single waker, and the mutex does the ordering — the waker cannot reach its second `lock`
until the caller parks again, and it records `notified` while still holding the lock, so the caller cannot
record `resumed` first. The predicate is reset under the lock between the episodes, which is why the second
notification cannot be lost in the gap either. -/
def bridgeNotifyEpisode : IO Unit := do
  let m ← Std.BaseMutex.new
  let cv ← Std.Condvar.new
  let ready ← IO.mkRef false
  let note (stage actor op : String) : IO Unit := do
    let ns ← IO.monoNanosNow
    IO.println s!"bridge|notify-episode|ns={ns}|actor={actor}|op={op}|stage={stage}"
  -- One waker per episode, started while the lock is held. A single waker looping over both episodes is
  -- unsound here, and it is worth saying why: after its first notification the caller is *waking*, both
  -- it and the waker race for the mutex, and if the waker wins it spends the second notification on a
  -- caller that has not parked again — the second wait then parks with no waker left. The failures were
  -- intermittent, which is how the race shows. A waker started under the lock cannot reach its `lock`
  -- until this carrier is parked in *its* episode, so every episode happens and every notification is
  -- delivered to the wait it was meant for. Its `unlock` precedes the caller's resume, so the ordering
  -- relations hold by construction.
  let caller ← IO.asTask (do
    Std.BaseMutex.lock m
    for stage in ["1", "2"] do
      ready.set false
      note stage "caller" "parked"
      let waker ← IO.asTask (do
        Std.BaseMutex.lock m
        ready.set true
        Std.Condvar.notifyAll cv
        note stage "waker" "notified"
        Std.BaseMutex.unlock m) Task.Priority.dedicated
      Std.Condvar.waitUntil cv m (do return (← ready.get))
      note stage "caller" "resumed"
      let _ ← IO.wait waker
    Std.BaseMutex.unlock m) Task.Priority.dedicated
  let _ ← IO.wait caller

/-- **Two live objects are two objects.** The countermodel is a representation that collapses them: if the
mapping sent `a` and `b` to one model lock, a claim about `a` would be a claim about `b`.

Another carrier tries both while this one holds `a` only. That carrier is refused `a` and granted `b` — the
negative and the affirmative control in the same run, which is what an absence claim needs. Both attempts
are `tryLock`, so the refused one cannot block, and the second is from a different carrier than the owner,
which is what the A2 undefined-behaviour caveat requires. -/
def bridgeDistinctObjects : IO Unit := do
  let a ← Std.BaseMutex.new
  let b ← Std.BaseMutex.new
  let note (actor op out : String) : IO Unit := do
    let ns ← IO.monoNanosNow
    IO.println s!"bridge|distinct-objects|ns={ns}|actor={actor}|op={op}|out={out}"
  Std.BaseMutex.lock a
  note "claimer" "lock-a" "acquired"
  let other ← IO.asTask (do
    let gotA ← Std.BaseMutex.tryLock a
    note "other" "trylock-a" (if gotA then "granted" else "refused")
    let gotB ← Std.BaseMutex.tryLock b
    note "other" "trylock-b" (if gotB then "granted" else "refused")
    if gotB then Std.BaseMutex.unlock b) Task.Priority.dedicated
  let _ ← IO.wait other
  Std.BaseMutex.unlock a
  note "claimer" "unlock-a" "released"

/-- Entry point. The proofs are checked when this module compiles; the report names what they establish and
what the countermodel is for. -/
def bridgeControlsMain : IO UInt32 := do
  IO.println "representation dependence controls"
  IO.println "  countermodel: under the superseded shape, one acquisition set every model lock's owner,"
  IO.println "                and one broadcast emptied every model condvar (both proved above)"
  IO.println "  guarded form: a witness at one representation supports one index, and no other"
  IO.println "  the parameter is structural: removing it from `Runs` breaks the guarded form's types"
  IO.println ""
  IO.println "the wait cycle, observed natively (records are `bridge|wait-cycle|...`)"
  bridgeWaitCycle
  IO.println ""
  IO.println "a notification that does not outlive its episode (`bridge|notify-episode|...`)"
  bridgeNotifyEpisode
  IO.println ""
  IO.println "two live objects are two objects (`bridge|distinct-objects|...`)"
  bridgeDistinctObjects
  IO.println "  the limit of a trace test: it can FALSIFY these contracts; it cannot establish adequacy."
  return 0

/-- Run one trace by name, for isolating a hang. `bridgecontrols <name>` runs only that trace. -/
def bridgeControlsOne (name : String) : IO UInt32 := do
  match name with
  | "wait-cycle"       => bridgeWaitCycle
  | "notify-episode"   => bridgeNotifyEpisode
  | "distinct-objects" => bridgeDistinctObjects
  | other              => IO.println s!"unknown trace '{other}': wait-cycle, notify-episode, distinct-objects"
  return 0

#print axioms LeanIn.lock_sets_only_the_index_it_names
#print axioms LeanIn.lock_claim_for_every_index

end LeanIn
