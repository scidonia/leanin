import Std

/-!
# The service, and its three obligations

The *product* half of [`docs/interface.md`](../../docs/interface.md), as Lean: the scheduler's
`LeanIn.Model.Scheduler` is the mechanism, this is what the service promises a caller. Everything
here is pure and decidable — the transitions are total functions returning `Option`, so `by decide`
*is* the executable reachability witness (no `LeanIn/Test/Dynamics.lean` extension is needed; that
probe exists for the `opaque` bridge relations, which these are not).

## The three obligations

* **No connection is silently dropped.** Every accepted connection is in exactly one of `live`,
  `completed`, `closed`: the three lists are pairwise disjoint and together number `admitted`
  (`Service.NoDrop`). This is why connections are *identities*, not counts — `close` terminates one
  connection and errors *that* connection's pending request, which a count abstraction cannot name.
* **The live count never exceeds the bound.** `Service.Bounded`; the bound is enforced by `accept`'s
  guard having *no transition* when it is reached — the shape `Sched.park` uses for its own guard.
* **Every request is answered or errored.** `Service.RequestsResolved`, with the outstanding ones
  inside the live set (`Service.PendingWithinLive`). `deadline` is the abstract clock — no wall
  clock appears in the model — and is enabled exactly for a pending request.

Each obligation has a **breaking control**: a plausible transition that destroys exactly it
(`abandon`, `acceptBeyondBound`, `closeDropping`), in the shape of
`enqueueWithoutWaking_breaks_live` in `LeanIn/Model/Scheduler.lean`.

## What is not claimed

Not the liveness half of "within its deadline" (that the timer *fires* is `Std.Async`'s leaf, and
`docs/primitive-theory.md` does not claim fairness or real time), and not the refinement of the
executor by this model (`docs/proof-strategy.md` P8, stated and deferred). The correspondence of
each operation to its executor event is argued in `docs/interface.md` §6.
-/

-- The `~` permutation notation is `scoped` inside `namespace List`.
open scoped List

namespace LeanIn

namespace Model

/-- A connection identity. Connections are identities rather than counts: closing is per-connection,
and a count abstraction could not say *which* connection's pending request a close errors. -/
abbrev ConnId := Nat

/-- The service state, abstracted to exactly what the three obligations care about.

`admitted` is the count the partition is taken against: how many connections have been accepted.
`cap` is the offered connections, the scenario's `n`, so the model can be shown exhausted. -/
structure Service where
  /-- The admission bound on live connections, constant. -/
  bound     : Nat := 0
  /-- Connections accepted so far: the partition's count. -/
  admitted  : Nat := 0
  /-- Accepted, not yet terminated. -/
  live      : List ConnId := []
  /-- Terminated by a normal completion. -/
  completed : List ConnId := []
  /-- Terminated without completing. -/
  closed    : List ConnId := []
  /-- Requests begun. -/
  requests  : Nat := 0
  /-- Requests answered. -/
  responded : Nat := 0
  /-- Requests given an error (deadline, or close). -/
  errored   : Nat := 0
  /-- Live connections owing a response (at most one each). -/
  pending   : List ConnId := []
  /-- Offered connections: the scenario's `n`. -/
  cap       : Nat := 1024
deriving Inhabited, Repr, DecidableEq

/-! ### The obligations, as definitions with content -/

/-- **Obligation 1, no silent drop.** The three terminal classes are pairwise disjoint and their
count equals the admitted count — but that is not yet a partition of the admitted connections, since
the ids are unconstrained: `admitted = 1` with `live = [7]` satisfies this definition. `WF`'s id bound
(every listed id below `admitted`) is the second half, and the two are conjoined wherever they are
used: `Service.Inv` is their conjunction, every preservation theorem is stated over `Inv`, and
`reachable_invariants` returns both. -/
def Service.NoDrop (s : Service) : Prop :=
  (s.live ++ s.completed ++ s.closed).Nodup ∧
  (s.live ++ s.completed ++ s.closed).length = s.admitted

/-- **Obligation 2, the bound.** The live count never exceeds the bound. -/
def Service.Bounded (s : Service) : Prop := s.live.length ≤ s.bound

/-- **Obligation 3, every request resolved.** Each request is answered, errored, or still pending:
the three counts account for all of them. -/
def Service.RequestsResolved (s : Service) : Prop :=
  s.responded + s.errored + s.pending.length = s.requests

/-- **Obligation 3, the pending ones are live.** A request can only be outstanding on a connection
that is still live, so its deadline can still fire. -/
def Service.PendingWithinLive (s : Service) : Prop := ∀ i ∈ s.pending, i ∈ s.live

/-- Well-formedness: a nonzero bound, no connection owing two responses, every listed connection
below the admitted count (so a fresh id is always available), and the counts agreeing. -/
def Service.WF (s : Service) : Prop :=
  0 < s.bound ∧ s.pending.Nodup ∧
  (∀ i ∈ s.live ++ s.completed ++ s.closed, i < s.admitted) ∧
  s.live.length + s.completed.length + s.closed.length = s.admitted

/-- The five invariants the reachable states carry. -/
def Service.Inv (s : Service) : Prop :=
  s.WF ∧ s.NoDrop ∧ s.Bounded ∧ s.RequestsResolved ∧ s.PendingWithinLive

/-- A fresh service: no connections, no requests. -/
def Service.initial (bound cap : Nat) : Service :=
  { bound := bound, cap := cap }

/-! ### The transitions

An operation that must not happen has **no transition**: `accept` refuses at the bound, `request`
refuses for an unknown or already-owing connection, and so on. -/

/-- Admit a connection. **Obligation 2 lives in this guard**: there is no transition when the live
count has reached the bound (the shape of `Sched.park`). The new id is `s.admitted`, fresh by
`WF`. -/
def Service.accept (s : Service) : Option Service :=
  if s.admitted < s.cap ∧ s.live.length < s.bound then
    some { s with admitted := s.admitted + 1, live := s.live ++ [s.admitted] }
  else none

/-- Begin one request on a live connection that owes none. -/
def Service.request (s : Service) (i : ConnId) : Option Service :=
  if i ∈ s.live ∧ i ∉ s.pending then
    some { s with requests := s.requests + 1, pending := s.pending ++ [i] }
  else none

/-- Answer a pending request. -/
def Service.respond (s : Service) (i : ConnId) : Option Service :=
  if i ∈ s.pending then
    some { s with responded := s.responded + 1, pending := s.pending.erase i }
  else none

/-- **The abstract clock.** Enabled exactly for a pending request, and it moves one request to
`errored`. The shape of `Sched.stop`: a named step, no wall clock. -/
def Service.deadline (s : Service) (i : ConnId) : Option Service :=
  if i ∈ s.pending then
    some { s with errored := s.errored + 1, pending := s.pending.erase i }
  else none

/-- Complete a live connection that owes no response: it leaves `live` for `completed`. -/
def Service.complete (s : Service) (i : ConnId) : Option Service :=
  if i ∈ s.live ∧ i ∉ s.pending then
    some { s with live := s.live.erase i, completed := s.completed ++ [i] }
  else none

/-- Close a live connection without completion: it leaves `live` for `closed`, and **any request it
owed is errored** — `close`'s `pending → errored`, the per-connection content of obligation 3. -/
def Service.close (s : Service) (i : ConnId) : Option Service :=
  if i ∈ s.live then
    some { s with live := s.live.erase i,
                  closed := s.closed ++ [i],
                  errored := if i ∈ s.pending then s.errored + 1 else s.errored,
                  pending := s.pending.erase i }
  else none

/-! ### The breaking controls

Each is a plausible transition that destroys exactly one obligation. -/

/-- **Drops** a live connection without recording it anywhere. Breaks `NoDrop`. -/
def Service.abandon (s : Service) (i : ConnId) : Option Service :=
  if i ∈ s.live then some { s with live := s.live.erase i } else none

/-- Admits **without the bound check**. Breaks `Bounded`. -/
def Service.acceptBeyondBound (s : Service) : Option Service :=
  if s.admitted < s.cap then
    some { s with admitted := s.admitted + 1, live := s.live ++ [s.admitted] }
  else none

/-- Terminates a connection and **forgets its pending request** (no `errored` increment). Breaks
`RequestsResolved`. -/
def Service.closeDropping (s : Service) (i : ConnId) : Option Service :=
  if i ∈ s.live then
    some { s with live := s.live.erase i, closed := s.closed ++ [i], pending := s.pending.erase i }
  else none

/-! ### List helpers -/

private theorem mem_left3 {i : ConnId} {l c x : List ConnId} (h : i ∈ l) : i ∈ l ++ c ++ x :=
  List.mem_append_left x (List.mem_append_left c h)

private theorem mem_mid3 {i : ConnId} {l c x : List ConnId} (h : i ∈ c) : i ∈ l ++ c ++ x :=
  List.mem_append_left x (List.mem_append_right l h)

private theorem mem_right3 {i : ConnId} {l c x : List ConnId} (h : i ∈ x) : i ∈ l ++ c ++ x :=
  List.mem_append_right (l ++ c) h

/-- `l.erase i ++ [i]` is `l` up to order: the element moved from wherever it was to the end. -/
private theorem erase_append_perm {i : ConnId} {l : List ConnId} (h : i ∈ l) :
    l.erase i ++ [i] ~ l :=
  ((List.perm_cons_erase h).trans
    (List.perm_append_comm (l₁ := [i]) (l₂ := l.erase i))).symm

/-- Inserting `a` at the front of `k` and appending `k` to `l` commutes. -/
private theorem perm_insert_last (l k : List ConnId) (a : ConnId) :
    (l ++ [a]) ++ k ~ (l ++ k) ++ [a] := by
  have h1 : (l ++ [a]) ++ k = l ++ ([a] ++ k) := List.append_assoc l [a] k
  have h2 : l ++ ([a] ++ k) ~ l ++ (k ++ [a]) :=
    List.Perm.append_left l (List.perm_append_comm (l₁ := [a]) (l₂ := k))
  have h3 : l ++ (k ++ [a]) = (l ++ k) ++ [a] := (List.append_assoc l k [a]).symm
  rw [h1, ← h3]
  exact h2

/-- **`complete`'s list surgery.** `i` leaves `live` and is appended to `completed`. -/
private theorem perm_erase_complete {i : ConnId} {l c x : List ConnId} (h : i ∈ l) :
    (l.erase i ++ (c ++ [i])) ++ x ~ (l ++ c) ++ x := by
  have he : l.erase i ++ [i] ~ l := erase_append_perm h
  have hk : (c ++ [i]) ++ x ~ [i] ++ (c ++ x) := by
    have := List.Perm.append_right x (List.perm_append_comm (l₁ := c) (l₂ := [i]))
    simpa only [List.append_assoc] using this
  have step : (l.erase i ++ (c ++ [i])) ++ x ~ l ++ (c ++ x) := by
    rw [List.append_assoc (l.erase i) (c ++ [i]) x]
    refine (List.Perm.append_left (l.erase i) hk).trans ?_
    rw [← List.append_assoc (l.erase i) [i] (c ++ x)]
    exact List.Perm.append_right (c ++ x) he
  rw [List.append_assoc l c x]
  exact step

/-- **`close`'s list surgery.** `i` leaves `live` and is appended to `closed`. -/
private theorem perm_erase_close {i : ConnId} {l c x : List ConnId} (h : i ∈ l) :
    (l.erase i ++ c) ++ (x ++ [i]) ~ (l ++ c) ++ x := by
  have he : l.erase i ++ [i] ~ l := erase_append_perm h
  have hk : c ++ (x ++ [i]) ~ [i] ++ (c ++ x) := by
    have := List.perm_append_comm (l₁ := c ++ x) (l₂ := [i])
    simpa only [List.append_assoc] using this
  have step : (l.erase i ++ c) ++ (x ++ [i]) ~ l ++ (c ++ x) := by
    rw [List.append_assoc (l.erase i) c (x ++ [i])]
    refine (List.Perm.append_left (l.erase i) hk).trans ?_
    rw [← List.append_assoc (l.erase i) [i] (c ++ x)]
    exact List.Perm.append_right (c ++ x) he
  rw [List.append_assoc l c x]
  exact step

/-- `NoDrop` after a permutation that preserves `admitted`. -/
private theorem noDrop_of_perm {s s' : Service}
    (h : s'.live ++ s'.completed ++ s'.closed ~ s.live ++ s.completed ++ s.closed)
    (hadm : s'.admitted = s.admitted) (hnd : s.NoDrop) : s'.NoDrop := by
  refine ⟨(List.Perm.nodup_iff h).mpr hnd.1, ?_⟩
  rw [List.Perm.length_eq h, hadm]
  exact hnd.2

/-- `NoDrop` after `accept`: the triple grows by the fresh id `s.admitted`, which `WF` places below
every listed connection id. -/
private theorem noDrop_of_perm_append {s s' : Service}
    (h : s'.live ++ s'.completed ++ s'.closed
          ~ (s.live ++ s.completed ++ s.closed) ++ [s.admitted])
    (hadm : s'.admitted = s.admitted + 1)
    (hids : ∀ i ∈ s.live ++ s.completed ++ s.closed, i < s.admitted)
    (hnd : s.NoDrop) : s'.NoDrop := by
  have hfresh : s.admitted ∉ s.live ++ s.completed ++ s.closed :=
    fun hm => Nat.lt_irrefl _ (hids s.admitted hm)
  have hnod : ((s.live ++ s.completed ++ s.closed) ++ [s.admitted]).Nodup := by
    rw [List.nodup_append]
    refine ⟨hnd.1, by simp, ?_⟩
    intro a ha b hb hab
    rw [List.mem_singleton] at hb
    exact hfresh (hb ▸ (hab ▸ ha))
  refine ⟨(List.Perm.nodup_iff h).mpr hnod, ?_⟩
  rw [List.Perm.length_eq h, List.length_append, List.length_singleton, hadm, hnd.2]

/-! ### The obligations are preserved -/

/-- `accept` preserves every invariant. -/
theorem accept_inv {s s' : Service} (h : s.Inv) (hs : s.accept = some s') : s'.Inv := by
  obtain ⟨hwf, hnd, hb, hrr, hpl⟩ := h
  obtain ⟨hbnd, hpnd, hids, hcnt⟩ := hwf
  unfold Service.accept at hs
  by_cases hc : s.admitted < s.cap ∧ s.live.length < s.bound
  · rw [ite_eq_left hc] at hs
    obtain ⟨_, hlt⟩ := hc
    injection hs with hseq
    have hl : s'.live = s.live ++ [s.admitted] := by simp only [← hseq]
    have hcomp : s'.completed = s.completed := by simp only [← hseq]
    have hx : s'.closed = s.closed := by simp only [← hseq]
    have ha : s'.admitted = s.admitted + 1 := by simp only [← hseq]
    have hp : s'.pending = s.pending := by simp only [← hseq]
    have hr : s'.requests = s.requests := by simp only [← hseq]
    have hresp : s'.responded = s.responded := by simp only [← hseq]
    have herr : s'.errored = s.errored := by simp only [← hseq]
    have hbd : s'.bound = s.bound := by simp only [← hseq]
    have hwf' : s'.WF := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hbd]; exact hbnd
      · rw [hp]; exact hpnd
      · intro i hi
        rw [hl, hcomp, hx] at hi
        rw [ha]
        rcases List.mem_append.mp hi with hi | hi
        · rcases List.mem_append.mp hi with hi | hi
          · rcases List.mem_append.mp hi with hi | hi
            · exact Nat.lt_succ_of_lt (hids i (mem_left3 hi))
            · rw [List.mem_singleton] at hi; rw [hi]; exact Nat.lt_succ_self _
          · exact Nat.lt_succ_of_lt (hids i (mem_mid3 hi))
        · exact Nat.lt_succ_of_lt (hids i (mem_right3 hi))
      · rw [hl, hcomp, hx, ha]
        have hL : (s.live ++ [s.admitted]).length = s.live.length + 1 := by simp
        omega
    have hnd' : s'.NoDrop := by
      refine noDrop_of_perm_append ?_ ha hids hnd
      rw [hl, hcomp, hx]
      exact (List.Perm.append_right s.closed (perm_insert_last s.live s.completed s.admitted)).trans
        (perm_insert_last (s.live ++ s.completed) s.closed s.admitted)
    have hb' : s'.Bounded := by
      unfold Service.Bounded at hb ⊢
      rw [hl, hbd]
      simp only [List.length_append, List.length_singleton]
      omega
    have hrr' : s'.RequestsResolved := by
      unfold Service.RequestsResolved at hrr ⊢
      rw [hresp, herr, hp, hr]
      exact hrr
    have hpl' : s'.PendingWithinLive := by
      intro i hi
      rw [hp] at hi
      rw [hl]
      exact List.mem_append_left _ (hpl i hi)
    exact ⟨hwf', hnd', hb', hrr', hpl'⟩
  · rw [ite_eq_right hc] at hs
    exact absurd hs (by simp)

/-- `request` preserves every invariant. -/
theorem request_inv {s s' : Service} {i : ConnId} (h : s.Inv) (hs : s.request i = some s') :
    s'.Inv := by
  obtain ⟨hwf, hnd, hb, hrr, hpl⟩ := h
  obtain ⟨hbnd, hpnd, hids, hcnt⟩ := hwf
  unfold Service.request at hs
  by_cases hc : i ∈ s.live ∧ i ∉ s.pending
  · rw [ite_eq_left hc] at hs
    obtain ⟨hlive, hnin⟩ := hc
    injection hs with hseq
    have hl : s'.live = s.live := by simp only [← hseq]
    have hcomp : s'.completed = s.completed := by simp only [← hseq]
    have hx : s'.closed = s.closed := by simp only [← hseq]
    have ha : s'.admitted = s.admitted := by simp only [← hseq]
    have hp : s'.pending = s.pending ++ [i] := by simp only [← hseq]
    have hr : s'.requests = s.requests + 1 := by simp only [← hseq]
    have hresp : s'.responded = s.responded := by simp only [← hseq]
    have herr : s'.errored = s.errored := by simp only [← hseq]
    have hbd : s'.bound = s.bound := by simp only [← hseq]
    have hwf' : s'.WF := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hbd]; exact hbnd
      · rw [hp]
        rw [List.nodup_append]
        refine ⟨hpnd, by simp, ?_⟩
        intro a ham b hb' hab
        rw [List.mem_singleton] at hb'
        exact hnin (hb' ▸ (hab ▸ ham))
      · rw [hl, hcomp, hx, ha]; exact hids
      · rw [hl, hcomp, hx, ha]; exact hcnt
    have hnd' : s'.NoDrop := by
      unfold Service.NoDrop at hnd ⊢
      rw [hl, hcomp, hx, ha]
      exact hnd
    have hb' : s'.Bounded := by
      unfold Service.Bounded at hb ⊢
      rw [hl, hbd]; exact hb
    have hrr' : s'.RequestsResolved := by
      unfold Service.RequestsResolved at hrr ⊢
      rw [hresp, herr, hp, hr]
      have : (s.pending ++ [i]).length = s.pending.length + 1 := by simp
      omega
    have hpl' : s'.PendingWithinLive := by
      intro j hj
      rw [hp] at hj
      rw [hl]
      rcases List.mem_append.mp hj with hj | hj
      · exact hpl j hj
      · rw [List.mem_singleton] at hj; rw [hj]; exact hlive
    exact ⟨hwf', hnd', hb', hrr', hpl'⟩
  · rw [ite_eq_right hc] at hs
    exact absurd hs (by simp)

/-- `respond` preserves every invariant. -/
theorem respond_inv {s s' : Service} {i : ConnId} (h : s.Inv) (hs : s.respond i = some s') :
    s'.Inv := by
  obtain ⟨hwf, hnd, hb, hrr, hpl⟩ := h
  obtain ⟨hbnd, hpnd, hids, hcnt⟩ := hwf
  unfold Service.respond at hs
  by_cases hc : i ∈ s.pending
  · rw [ite_eq_left hc] at hs
    injection hs with hseq
    have hl : s'.live = s.live := by simp only [← hseq]
    have hcomp : s'.completed = s.completed := by simp only [← hseq]
    have hx : s'.closed = s.closed := by simp only [← hseq]
    have ha : s'.admitted = s.admitted := by simp only [← hseq]
    have hp : s'.pending = s.pending.erase i := by simp only [← hseq]
    have hr : s'.requests = s.requests := by simp only [← hseq]
    have hresp : s'.responded = s.responded + 1 := by simp only [← hseq]
    have herr : s'.errored = s.errored := by simp only [← hseq]
    have hbd : s'.bound = s.bound := by simp only [← hseq]
    have hwf' : s'.WF := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hbd]; exact hbnd
      · rw [hp]; exact hpnd.erase i
      · rw [hl, hcomp, hx, ha]; exact hids
      · rw [hl, hcomp, hx, ha]; exact hcnt
    have hnd' : s'.NoDrop := by
      unfold Service.NoDrop at hnd ⊢
      rw [hl, hcomp, hx, ha]; exact hnd
    have hb' : s'.Bounded := by
      unfold Service.Bounded at hb ⊢
      rw [hl, hbd]; exact hb
    have hrr' : s'.RequestsResolved := by
      unfold Service.RequestsResolved at hrr ⊢
      rw [hresp, herr, hp, hr, List.length_erase_of_mem hc]
      have := List.length_pos_of_mem hc
      omega
    have hpl' : s'.PendingWithinLive := by
      intro j hj
      rw [hp] at hj
      rw [hl]
      exact hpl j (List.mem_of_mem_erase hj)
    exact ⟨hwf', hnd', hb', hrr', hpl'⟩
  · rw [ite_eq_right hc] at hs
    exact absurd hs (by simp)

/-- `deadline` preserves every invariant. -/
theorem deadline_inv {s s' : Service} {i : ConnId} (h : s.Inv) (hs : s.deadline i = some s') :
    s'.Inv := by
  obtain ⟨hwf, hnd, hb, hrr, hpl⟩ := h
  obtain ⟨hbnd, hpnd, hids, hcnt⟩ := hwf
  unfold Service.deadline at hs
  by_cases hc : i ∈ s.pending
  · rw [ite_eq_left hc] at hs
    injection hs with hseq
    have hl : s'.live = s.live := by simp only [← hseq]
    have hcomp : s'.completed = s.completed := by simp only [← hseq]
    have hx : s'.closed = s.closed := by simp only [← hseq]
    have ha : s'.admitted = s.admitted := by simp only [← hseq]
    have hp : s'.pending = s.pending.erase i := by simp only [← hseq]
    have hr : s'.requests = s.requests := by simp only [← hseq]
    have hresp : s'.responded = s.responded := by simp only [← hseq]
    have herr : s'.errored = s.errored + 1 := by simp only [← hseq]
    have hbd : s'.bound = s.bound := by simp only [← hseq]
    have hwf' : s'.WF := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hbd]; exact hbnd
      · rw [hp]; exact hpnd.erase i
      · rw [hl, hcomp, hx, ha]; exact hids
      · rw [hl, hcomp, hx, ha]; exact hcnt
    have hnd' : s'.NoDrop := by
      unfold Service.NoDrop at hnd ⊢
      rw [hl, hcomp, hx, ha]; exact hnd
    have hb' : s'.Bounded := by
      unfold Service.Bounded at hb ⊢
      rw [hl, hbd]; exact hb
    have hrr' : s'.RequestsResolved := by
      unfold Service.RequestsResolved at hrr ⊢
      rw [hresp, herr, hp, hr, List.length_erase_of_mem hc]
      have := List.length_pos_of_mem hc
      omega
    have hpl' : s'.PendingWithinLive := by
      intro j hj
      rw [hp] at hj
      rw [hl]
      exact hpl j (List.mem_of_mem_erase hj)
    exact ⟨hwf', hnd', hb', hrr', hpl'⟩
  · rw [ite_eq_right hc] at hs
    exact absurd hs (by simp)

/-- `complete` preserves every invariant. -/
theorem complete_inv {s s' : Service} {i : ConnId} (h : s.Inv) (hs : s.complete i = some s') :
    s'.Inv := by
  obtain ⟨hwf, hnd, hb, hrr, hpl⟩ := h
  obtain ⟨hbnd, hpnd, hids, hcnt⟩ := hwf
  unfold Service.complete at hs
  by_cases hc : i ∈ s.live ∧ i ∉ s.pending
  · rw [ite_eq_left hc] at hs
    obtain ⟨hlive, hnin⟩ := hc
    injection hs with hseq
    have hl : s'.live = s.live.erase i := by simp only [← hseq]
    have hcomp : s'.completed = s.completed ++ [i] := by simp only [← hseq]
    have hx : s'.closed = s.closed := by simp only [← hseq]
    have ha : s'.admitted = s.admitted := by simp only [← hseq]
    have hp : s'.pending = s.pending := by simp only [← hseq]
    have hr : s'.requests = s.requests := by simp only [← hseq]
    have hresp : s'.responded = s.responded := by simp only [← hseq]
    have herr : s'.errored = s.errored := by simp only [← hseq]
    have hbd : s'.bound = s.bound := by simp only [← hseq]
    have hwf' : s'.WF := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hbd]; exact hbnd
      · rw [hp]; exact hpnd
      · intro j hj
        rw [hl, hcomp, hx] at hj
        rw [ha]
        rcases List.mem_append.mp hj with hj | hj
        · rcases List.mem_append.mp hj with hj | hj
          · exact hids j (mem_left3 (List.mem_of_mem_erase hj))
          · rcases List.mem_append.mp hj with hj | hj
            · exact hids j (mem_mid3 hj)
            · rw [List.mem_singleton] at hj; rw [hj]; exact hids i (mem_left3 hlive)
        · exact hids j (mem_right3 hj)
      · rw [hl, hcomp, hx, ha]
        have hL : (s.live.erase i).length = s.live.length - 1 := List.length_erase_of_mem hlive
        have hC : (s.completed ++ [i]).length = s.completed.length + 1 := by simp
        have hpos := List.length_pos_of_mem hlive
        omega
    have hnd' : s'.NoDrop := by
      refine noDrop_of_perm ?_ ha hnd
      rw [hl, hcomp, hx]
      exact perm_erase_complete hlive
    have hb' : s'.Bounded := by
      unfold Service.Bounded at hb ⊢
      rw [hl, hbd]
      have := List.length_erase_le (a := i) (l := s.live)
      omega
    have hrr' : s'.RequestsResolved := by
      unfold Service.RequestsResolved at hrr ⊢
      rw [hresp, herr, hp, hr]; exact hrr
    have hpl' : s'.PendingWithinLive := by
      intro j hj
      rw [hp] at hj
      rw [hl]
      have hne : j ≠ i := fun hji => hnin (hji ▸ hj)
      exact (List.mem_erase_of_ne hne).mpr (hpl j hj)
    exact ⟨hwf', hnd', hb', hrr', hpl'⟩
  · rw [ite_eq_right hc] at hs
    exact absurd hs (by simp)

/-- `close` preserves every invariant. The nested `if` is the per-connection content of obligation
3: only *this* connection's pending request is errored. -/
theorem close_inv {s s' : Service} {i : ConnId} (h : s.Inv) (hs : s.close i = some s') : s'.Inv := by
  obtain ⟨hwf, hnd, hb, hrr, hpl⟩ := h
  obtain ⟨hbnd, hpnd, hids, hcnt⟩ := hwf
  unfold Service.close at hs
  by_cases hlive : i ∈ s.live
  · rw [ite_eq_left hlive] at hs
    injection hs with hseq
    have hl : s'.live = s.live.erase i := by simp only [← hseq]
    have hcomp : s'.completed = s.completed := by simp only [← hseq]
    have hx : s'.closed = s.closed ++ [i] := by simp only [← hseq]
    have ha : s'.admitted = s.admitted := by simp only [← hseq]
    have hp : s'.pending = s.pending.erase i := by simp only [← hseq]
    have hr : s'.requests = s.requests := by simp only [← hseq]
    have hresp : s'.responded = s.responded := by simp only [← hseq]
    have hbd : s'.bound = s.bound := by simp only [← hseq]
    have hwf' : s'.WF := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hbd]; exact hbnd
      · rw [hp]; exact hpnd.erase i
      · intro j hj
        rw [hl, hcomp, hx] at hj
        rw [ha]
        rcases List.mem_append.mp hj with hj | hj
        · rcases List.mem_append.mp hj with hj | hj
          · exact hids j (mem_left3 (List.mem_of_mem_erase hj))
          · exact hids j (mem_mid3 hj)
        · rcases List.mem_append.mp hj with hj | hj
          · exact hids j (mem_right3 hj)
          · rw [List.mem_singleton] at hj; rw [hj]; exact hids i (mem_left3 hlive)
      · rw [hl, hcomp, hx, ha]
        have hL : (s.live.erase i).length = s.live.length - 1 := List.length_erase_of_mem hlive
        have hC : (s.closed ++ [i]).length = s.closed.length + 1 := by simp
        have hpos := List.length_pos_of_mem hlive
        omega
    have hnd' : s'.NoDrop := by
      refine noDrop_of_perm ?_ ha hnd
      rw [hl, hcomp, hx]
      exact perm_erase_close hlive
    have hb' : s'.Bounded := by
      unfold Service.Bounded at hb ⊢
      rw [hl, hbd]
      have := List.length_erase_le (a := i) (l := s.live)
      omega
    have hpl' : s'.PendingWithinLive := by
      intro j hj
      rw [hp] at hj
      rw [hl]
      obtain ⟨hne, hjmem⟩ := (hpnd.mem_erase_iff).mp hj
      exact (List.mem_erase_of_ne hne).mpr (hpl j hjmem)
    by_cases hpin : i ∈ s.pending
    · have herr : s'.errored = s.errored + 1 := by
        rw [← hseq]
        show (if i ∈ s.pending then s.errored + 1 else s.errored) = s.errored + 1
        exact ite_eq_left hpin
      have hrr' : s'.RequestsResolved := by
        unfold Service.RequestsResolved at hrr ⊢
        rw [hresp, herr, hp, hr, List.length_erase_of_mem hpin]
        have := List.length_pos_of_mem hpin
        omega
      exact ⟨hwf', hnd', hb', hrr', hpl'⟩
    · have herr : s'.errored = s.errored := by
        rw [← hseq]
        show (if i ∈ s.pending then s.errored + 1 else s.errored) = s.errored
        exact ite_eq_right hpin
      have hp' : s'.pending = s.pending := by rw [hp, List.erase_of_not_mem hpin]
      have hrr' : s'.RequestsResolved := by
        unfold Service.RequestsResolved at hrr ⊢
        rw [hresp, herr, hp', hr]; exact hrr
      exact ⟨hwf', hnd', hb', hrr', hpl'⟩
  · rw [ite_eq_right hlive] at hs
    exact absurd hs (by simp)

/-! ### Per-obligation statements, for each transition

"Each preserves each invariant", named so a reader can cite one directly. -/

theorem accept_noDrop {s s' : Service} (h : s.Inv) (hs : s.accept = some s') : s'.NoDrop :=
  (accept_inv h hs).2.1
theorem accept_bounded {s s' : Service} (h : s.Inv) (hs : s.accept = some s') : s'.Bounded :=
  (accept_inv h hs).2.2.1
theorem accept_requests {s s' : Service} (h : s.Inv) (hs : s.accept = some s') : s'.RequestsResolved :=
  (accept_inv h hs).2.2.2.1
theorem accept_pending {s s' : Service} (h : s.Inv) (hs : s.accept = some s') : s'.PendingWithinLive :=
  (accept_inv h hs).2.2.2.2

theorem request_noDrop {s s' : Service} {i : ConnId} (h : s.Inv) (hs : s.request i = some s') : s'.NoDrop :=
  (request_inv h hs).2.1
theorem request_bounded {s s' : Service} {i : ConnId} (h : s.Inv) (hs : s.request i = some s') : s'.Bounded :=
  (request_inv h hs).2.2.1
theorem request_requests {s s' : Service} {i : ConnId} (h : s.Inv) (hs : s.request i = some s') : s'.RequestsResolved :=
  (request_inv h hs).2.2.2.1
theorem request_pending {s s' : Service} {i : ConnId} (h : s.Inv) (hs : s.request i = some s') : s'.PendingWithinLive :=
  (request_inv h hs).2.2.2.2

theorem respond_noDrop {s s' : Service} {i : ConnId} (h : s.Inv) (hs : s.respond i = some s') : s'.NoDrop :=
  (respond_inv h hs).2.1
theorem respond_bounded {s s' : Service} {i : ConnId} (h : s.Inv) (hs : s.respond i = some s') : s'.Bounded :=
  (respond_inv h hs).2.2.1
theorem respond_requests {s s' : Service} {i : ConnId} (h : s.Inv) (hs : s.respond i = some s') : s'.RequestsResolved :=
  (respond_inv h hs).2.2.2.1
theorem respond_pending {s s' : Service} {i : ConnId} (h : s.Inv) (hs : s.respond i = some s') : s'.PendingWithinLive :=
  (respond_inv h hs).2.2.2.2

theorem deadline_noDrop {s s' : Service} {i : ConnId} (h : s.Inv) (hs : s.deadline i = some s') : s'.NoDrop :=
  (deadline_inv h hs).2.1
theorem deadline_bounded {s s' : Service} {i : ConnId} (h : s.Inv) (hs : s.deadline i = some s') : s'.Bounded :=
  (deadline_inv h hs).2.2.1
theorem deadline_requests {s s' : Service} {i : ConnId} (h : s.Inv) (hs : s.deadline i = some s') :
    s'.RequestsResolved :=
  (deadline_inv h hs).2.2.2.1
theorem deadline_pending {s s' : Service} {i : ConnId} (h : s.Inv) (hs : s.deadline i = some s') :
    s'.PendingWithinLive :=
  (deadline_inv h hs).2.2.2.2

theorem complete_noDrop {s s' : Service} {i : ConnId} (h : s.Inv) (hs : s.complete i = some s') : s'.NoDrop :=
  (complete_inv h hs).2.1
theorem complete_bounded {s s' : Service} {i : ConnId} (h : s.Inv) (hs : s.complete i = some s') : s'.Bounded :=
  (complete_inv h hs).2.2.1
theorem complete_requests {s s' : Service} {i : ConnId} (h : s.Inv) (hs : s.complete i = some s') : s'.RequestsResolved :=
  (complete_inv h hs).2.2.2.1
theorem complete_pending {s s' : Service} {i : ConnId} (h : s.Inv) (hs : s.complete i = some s') : s'.PendingWithinLive :=
  (complete_inv h hs).2.2.2.2

theorem close_noDrop {s s' : Service} {i : ConnId} (h : s.Inv) (hs : s.close i = some s') : s'.NoDrop :=
  (close_inv h hs).2.1
theorem close_bounded {s s' : Service} {i : ConnId} (h : s.Inv) (hs : s.close i = some s') : s'.Bounded :=
  (close_inv h hs).2.2.1
theorem close_requests {s s' : Service} {i : ConnId} (h : s.Inv) (hs : s.close i = some s') : s'.RequestsResolved :=
  (close_inv h hs).2.2.2.1
theorem close_pending {s s' : Service} {i : ConnId} (h : s.Inv) (hs : s.close i = some s') : s'.PendingWithinLive :=
  (close_inv h hs).2.2.2.2

/-! ### Reachability

The right strength: the obligations are claimed of the states the service can actually produce, not
of arbitrary well-formed states (a well-formed state can have too many live connections; see the
negative witness below). -/

inductive Service.Reachable : Service → Prop where
  | init (bound cap : Nat) (h : 0 < bound) : Reachable (Service.initial bound cap)
  | accept {s s'} : Reachable s → s.accept = some s' → Reachable s'
  | request {s s'} (i : ConnId) : Reachable s → s.request i = some s' → Reachable s'
  | respond {s s'} (i : ConnId) : Reachable s → s.respond i = some s' → Reachable s'
  | deadline {s s'} (i : ConnId) : Reachable s → s.deadline i = some s' → Reachable s'
  | complete {s s'} (i : ConnId) : Reachable s → s.complete i = some s' → Reachable s'
  | close {s s'} (i : ConnId) : Reachable s → s.close i = some s' → Reachable s'

/-- **The three obligations, over every reachable state.** -/
theorem reachable_invariants {s : Service} (h : Service.Reachable s) :
    s.WF ∧ s.NoDrop ∧ s.Bounded ∧ s.RequestsResolved ∧ s.PendingWithinLive := by
  induction h with
  | init bound cap hb =>
    refine ⟨⟨hb, by simp [Service.initial], by simp [Service.initial], by simp [Service.initial]⟩,
      ⟨by simp [Service.initial], by simp [Service.initial]⟩,
      by simp [Service.Bounded, Service.initial],
      by simp [Service.RequestsResolved, Service.initial],
      by simp [Service.PendingWithinLive, Service.initial]⟩
  | accept _ hs ih => exact accept_inv ih hs
  | request i _ hs ih => exact request_inv ih hs
  | respond i _ hs ih => exact respond_inv ih hs
  | deadline i _ hs ih => exact deadline_inv ih hs
  | complete i _ hs ih => exact complete_inv ih hs
  | close i _ hs ih => exact close_inv ih hs

/-- **Obligation 1**: no reachable state silently drops a connection. -/
theorem reachable_noDrop {s : Service} (h : Service.Reachable s) : s.NoDrop :=
  (reachable_invariants h).2.1

/-- **Obligation 2**: the live count never exceeds the bound. -/
theorem reachable_bounded {s : Service} (h : Service.Reachable s) : s.Bounded :=
  (reachable_invariants h).2.2.1

/-- **Obligation 3**: every reachable state's requests are all answered, errored, or pending. -/
theorem reachable_requests {s : Service} (h : Service.Reachable s) : s.RequestsResolved :=
  (reachable_invariants h).2.2.2.1

/-- **Obligation 3**: and the pending ones are live, so the deadline can still reach them. -/
theorem reachable_pendingWithinLive {s : Service} (h : Service.Reachable s) :
    s.PendingWithinLive :=
  (reachable_invariants h).2.2.2.2

/-! ### The obligations are not vacuous

Positive witnesses (reachable states that populate each claimed quantity) and negative witnesses
(states satisfying the *weaker* hypotheses while violating an obligation, so reachability is doing
real work). -/

/-- Positive: the bound is reachable at equality, and the next admission is then refused — the guard
of `accept` is not advisory. -/
example : ∃ s : Service, Service.Reachable s ∧ s.live.length = s.bound ∧ s.accept = none := by
  refine ⟨{ bound := 1, cap := 1024, admitted := 1, live := [0] }, ?_, by decide, by decide⟩
  exact Service.Reachable.accept
    (s' := { bound := 1, cap := 1024, admitted := 1, live := [0] })
    (Service.Reachable.init 1 1024 (by decide)) (by decide)

/-- Positive: a reachable state with both `completed` and `closed` populated — the partition of
obligation 1 really has all three classes in use. -/
example : ∃ s : Service, Service.Reachable s ∧ s.completed ≠ [] ∧ s.closed ≠ [] := by
  have h1 : Service.Reachable { bound := 2, cap := 1024, admitted := 1, live := [0] } :=
    Service.Reachable.accept
      (s' := { bound := 2, cap := 1024, admitted := 1, live := [0] })
      (Service.Reachable.init 2 1024 (by decide)) (by decide)
  have h2 : Service.Reachable { bound := 2, cap := 1024, admitted := 2, live := [0, 1] } :=
    Service.Reachable.accept
      (s := { bound := 2, cap := 1024, admitted := 1, live := [0] })
      (s' := { bound := 2, cap := 1024, admitted := 2, live := [0, 1] }) h1 (by decide)
  have h3 : Service.Reachable
      { bound := 2, cap := 1024, admitted := 2, live := [1], completed := [0] } :=
    Service.Reachable.complete
      (s := { bound := 2, cap := 1024, admitted := 2, live := [0, 1] })
      (s' := { bound := 2, cap := 1024, admitted := 2, live := [1], completed := [0] }) 0 h2
      (by decide)
  have h4 : Service.Reachable
      { bound := 2, cap := 1024, admitted := 2, completed := [0], closed := [1] } :=
    Service.Reachable.close
      (s := { bound := 2, cap := 1024, admitted := 2, live := [1], completed := [0] })
      (s' := { bound := 2, cap := 1024, admitted := 2, completed := [0], closed := [1] }) 1 h3
      (by decide)
  exact ⟨_, h4, by decide, by decide⟩

/-- Positive: a `deadline` resolution is reachable — the abstract clock can be taken into account. -/
example : ∃ s : Service, Service.Reachable s ∧ s.errored = 1 ∧ s.pending = [] := by
  have h1 : Service.Reachable { bound := 1, cap := 1024, admitted := 1, live := [0] } :=
    Service.Reachable.accept
      (s' := { bound := 1, cap := 1024, admitted := 1, live := [0] })
      (Service.Reachable.init 1 1024 (by decide)) (by decide)
  have h2 : Service.Reachable
      { bound := 1, cap := 1024, admitted := 1, live := [0], requests := 1, pending := [0] } :=
    Service.Reachable.request
      (s := { bound := 1, cap := 1024, admitted := 1, live := [0] })
      (s' := { bound := 1, cap := 1024, admitted := 1, live := [0], requests := 1,
               pending := [0] }) 0 h1 (by decide)
  have h3 : Service.Reachable
      { bound := 1, cap := 1024, admitted := 1, live := [0], requests := 1, errored := 1 } :=
    Service.Reachable.deadline
      (s := { bound := 1, cap := 1024, admitted := 1, live := [0], requests := 1,
              pending := [0] })
      (s' := { bound := 1, cap := 1024, admitted := 1, live := [0], requests := 1,
               errored := 1 }) 0 h2 (by decide)
  exact ⟨_, h3, by decide, by decide⟩

/-- Negative: `Bounded` is strictly stronger than `WF` — this well-formed state has `live.length =
bound + 1`, so `reachable_bounded` is doing work rather than being implied by well-formedness. -/
example : ∃ s : Service, s.WF ∧ ¬ s.Bounded :=
  ⟨{ bound := 1, admitted := 2, live := [0, 1] },
   by unfold Service.WF; decide, by unfold Service.Bounded; decide⟩

/-- Negative: `NoDrop` is not implied by `WF` — the same connection appears in `live` and
`completed`. -/
example : ∃ s : Service, s.WF ∧ ¬ s.NoDrop :=
  ⟨{ bound := 2, admitted := 2, live := [0], completed := [0] },
   by unfold Service.WF; decide, by unfold Service.NoDrop; decide⟩

/-- Negative: `RequestsResolved` is not implied by `WF`. -/
example : ∃ s : Service, s.WF ∧ ¬ s.RequestsResolved :=
  ⟨{ bound := 1, requests := 1 },
   by unfold Service.WF; decide, by unfold Service.RequestsResolved; decide⟩

/-- Negative: `PendingWithinLive` is not implied by `WF` — a pending request on a terminated
connection. -/
example : ∃ s : Service, s.WF ∧ ¬ s.PendingWithinLive :=
  ⟨{ bound := 1, admitted := 1, closed := [0], pending := [0] },
   by unfold Service.WF; decide, by unfold Service.PendingWithinLive; decide⟩

/-! ### The breaking controls

Each names the violation its transition causes, in the shape of `enqueueWithoutWaking_breaks_live`:
a well-formed state satisfying the obligation, on which the plausible transition destroys exactly
that obligation. -/

/-- **`abandon` breaks obligation 1.** A live connection is dropped without being recorded, so the
partition no longer accounts for `admitted`. -/
theorem abandon_breaks_noDrop :
    ∃ s s' : Service, s.WF ∧ s.NoDrop ∧ s.abandon 0 = some s' ∧ ¬ s'.NoDrop :=
  ⟨{ bound := 2, admitted := 1, live := [0] },
   { bound := 2, admitted := 1 },
   by unfold Service.WF; decide,
   by unfold Service.NoDrop; decide,
   by decide,
   by unfold Service.NoDrop; decide⟩

/-- **`acceptBeyondBound` breaks obligation 2.** Dropping `accept`'s bound clause admits past it. -/
theorem acceptBeyondBound_breaks_bounded :
    ∃ s s' : Service, s.WF ∧ s.Bounded ∧ s.acceptBeyondBound = some s' ∧ ¬ s'.Bounded :=
  ⟨{ bound := 1, admitted := 1, live := [0] },
   { bound := 1, admitted := 2, live := [0, 1] },
   by unfold Service.WF; decide,
   by unfold Service.Bounded; decide,
   by decide,
   by unfold Service.Bounded; decide⟩

/-- **`closeDropping` breaks obligation 3.** Terminating a connection without errored its pending
request leaves that request neither answered, errored, nor pending. -/
theorem closeDropping_breaks_requests :
    ∃ s s' : Service, s.WF ∧ s.RequestsResolved ∧ s.closeDropping 0 = some s' ∧
      ¬ s'.RequestsResolved :=
  ⟨{ bound := 1, admitted := 1, live := [0], requests := 1, pending := [0] },
   { bound := 1, admitted := 1, closed := [0], requests := 1 },
   by unfold Service.WF; decide,
   by unfold Service.RequestsResolved; decide,
   by decide,
   by unfold Service.RequestsResolved; decide⟩

-- The audit: the service's theorems rest on nothing beyond Lean's own axioms.
#print axioms LeanIn.Model.accept_inv
#print axioms LeanIn.Model.request_inv
#print axioms LeanIn.Model.respond_inv
#print axioms LeanIn.Model.deadline_inv
#print axioms LeanIn.Model.complete_inv
#print axioms LeanIn.Model.close_inv
#print axioms LeanIn.Model.reachable_invariants
#print axioms LeanIn.Model.reachable_noDrop
#print axioms LeanIn.Model.reachable_bounded
#print axioms LeanIn.Model.reachable_requests
#print axioms LeanIn.Model.reachable_pendingWithinLive
#print axioms LeanIn.Model.abandon_breaks_noDrop
#print axioms LeanIn.Model.acceptBeyondBound_breaks_bounded
#print axioms LeanIn.Model.closeDropping_breaks_requests

end Model

end LeanIn
