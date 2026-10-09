import Std
import LeanIn.Data.Ring
import LeanIn.Model.Pool

/-!
# The pool, as the implementation keeps it

M3's refinement target. `LeanIn.Model.Pool` is the specification and this is the structure an executor
actually holds, so the file is built around the **projection** `toModel` and the commutation facts that make
"the implementation does what the model does" a theorem rather than an intention.

The ring is `LeanIn.Data.Ring` (M2b) rather than a `List`, because the model's `ring` is *bounded* and a
`List` would turn the capacity into a claim. `Ring.toList` is the ghost view the projection reads — the live
elements, oldest first — so `push` is the back-append and `pop` the front-take.

Two things are deliberately not here. The wake protocol lives in `Scheduler`, and the script driver that
produces the executor's records lives with the client. The overflow's commutation, by contrast, is here and
unconditional: `Ring.keepFirst` sheds the newer half by index — the live count moves and nothing is copied —
so the halves this implementation keeps and evicts are the model's `take` and `drop` of its list.
`toModel_toRing` states that, and `toModel_submit` and `toModel_spawn` apply it to the two operations that
place work.
-/

namespace LeanIn.Sched

-- `Ring`'s operations need `Inhabited α` (`toList` falls back to `default`), and this pool is built on
-- them, so the instance travels with the type rather than being repeated at every mention of `Pool`.
variable {α : Type} [Inhabited α]

/-- The implementation's pool. Same fields as `LeanIn.Model.Pool`, with the ring as a container rather
than a list. -/
structure Pool (α : Type) (cap : Nat) where
  /-- The bounded FIFO ring: submitted at the back, taken from the front. -/
  ring      : Ring α cap
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
  /-- LIFO polls allowed per tick. 3 in Tokio. -/
  lifoCap   : Nat := 3
deriving Inhabited, Repr

/-- A fresh pool: an empty ring of `cap` slots and nothing held. -/
def emptyPool (α : Type) (cap : Nat) : Pool α cap :=
  { ring := emptyRing α cap }

/-- Work held somewhere: the ring, the LIFO slot, or `inject`. Reads the container's size, which is
`toList.length` — the projection's first obligation rather than an assumption. -/
def Pool.inFlight (p : Pool α cap) : Nat :=
  p.ring.size + (if p.lifo.isSome then 1 else 0) + p.inject.length

/-- **The projection.** The implementation's state as the specification describes it. "`Impl.push ⊑
Model.push`" is a statement about this function and `Pool.submit` below. -/
def Pool.toModel (p : Pool α cap) : Model.Pool α :=
  { ring      := p.ring.toList
    lifo      := p.lifo
    lifoPolls := p.lifoPolls
    inject    := p.inject
    pushed    := p.pushed
    taken     := p.taken
    cap       := cap
    lifoCap   := p.lifoCap }

/-- The owner's take, ignoring the allowance: ring first, then `inject`. A thief uses this too, which is
where "the LIFO slot is never stolen" comes from — this function cannot see `p.lifo`. -/
def Pool.takeFromRing (p : Pool α cap) : Option α × Pool α cap :=
  match p.ring.pop with
  | (some x, r) => (some x, { p with ring := r, taken := p.taken + 1 })
  | (none, _) =>
    match p.inject with
    | x :: rest => (some x, { p with inject := rest, taken := p.taken + 1 })
    | []        => (none, p)

/-- **Which way a take's decision went.** The model's `take` does not distinguish these, because none of
its claims need to; a *report* does, because the tick's allowance is observable only through which decision
served the take. -/
inductive Served where
  /-- The LIFO slot served the take: a poll inside the tick's allowance. -/
  | slot
  /-- The slot was occupied with the allowance spent, so this decision flushed it to `inject` and served the
  ring. -/
  | flushed
  /-- Neither: the ring, or `inject` once the ring was empty. -/
  | queue
deriving Repr, BEq, DecidableEq

/-- **A take and the decision it made.** `observed` is the LIFO slot's occupant as the decision read it,
taken inside the same expression that decides — so it is this pool's record of that instant, not a reading
taken beside it — and `served` says which way the decision went. `item` and `pool` are the take itself.

The client's records are read through this because the allowance has no other observable: a pool that never
populated the slot would report `none` at every decision, and one that kept polling past its cap would report
a fourth `slot`. -/
structure TakeReport (α : Type) (cap : Nat) where
  /-- The LIFO slot's occupant before this take, as the decision observed it. -/
  observed : Option α
  /-- Which way the decision went. -/
  served   : Served
  /-- The item taken, if any. -/
  item     : Option α
  /-- The pool after the take. -/
  pool     : Pool α cap

/-- The owner's take, with the decision it made.

The LIFO slot is preferred while the tick's allowance lasts; **when the allowance runs out with a task still
in the slot, the slot is flushed to `inject` before the ring is consulted**, so the allowance cannot strand
it. -/
def Pool.takeReport (p : Pool α cap) : TakeReport α cap :=
  if p.lifoPolls < p.lifoCap then
    match p.lifo with
    | some x => { observed := some x, served := .slot, item := some x,
                  pool := { p with lifo := none, lifoPolls := p.lifoPolls + 1, taken := p.taken + 1 } }
    | none   =>
      let r := p.takeFromRing
      { observed := none, served := .queue, item := r.1, pool := r.2 }
  else
    match p.lifo with
    | some x =>
      let flushed := { p with lifo := none, inject := p.inject ++ [x] }
      let r := flushed.takeFromRing
      { observed := some x, served := .flushed, item := r.1, pool := r.2 }
    | none   =>
      let r := p.takeFromRing
      { observed := none, served := .queue, item := r.1, pool := r.2 }

/-- The owner's take: the decision without its report. One definition of the decision, so the two cannot
drift — the report is what the record reads, and this is what the worker uses. -/
def Pool.take (p : Pool α cap) : Option α × Pool α cap :=
  let r := p.takeReport
  (r.item, r.pool)

/-- A tick: the LIFO allowance refreshes. -/
def Pool.tick (p : Pool α cap) : Pool α cap := { p with lifoPolls := 0 }

/-- **Where a task goes when it joins the ring** — the implementation's `Model.Pool.toRing`. Append at the
back if there is room. Otherwise the *newer* half leaves for `inject` and the *older* half stays with the new
task: intake places work in the first half, so anything found in the second is provably not freshly intaken.

Factored out so `spawn` places the task its LIFO slot displaces by the same rule, and there is one overflow
rather than two that can drift. It does not count: the task was counted when it entered the pool. -/
def Pool.toRing (p : Pool α cap) (x : α) : Pool α cap :=
  if p.ring.size < cap then
    { p with ring := p.ring.push x }
  else
    -- The newer half leaves by *moving the live count*, not by reading the ring out and rebuilding it: the
    -- shed elements are at the back of the live range, and `WF` says only the live range is read, so nothing
    -- is copied and nothing is refilled. The one read of `toList` is over what is still held, and
    -- `live.drop half` is exactly the list the specification moves to `inject`.
    let half := p.ring.size / 2
    let live := p.ring.toList
    { p with ring   := (p.ring.keepFirst half).push x,
             inject := p.inject ++ live.drop half }

/-- **Submit, with overflow**: the placement rule, and the count. -/
def Pool.submit (p : Pool α cap) (x : α) : Pool α cap :=
  { p.toRing x with pushed := p.pushed + 1 }

/-- **Spawn, owner-local.** The new task takes the LIFO slot; the task it displaces goes to the run queue by
the same rule a submit uses, overflow included, so displacing it cannot silently drop it —
`schedule_local`, `worker.rs:1398`. -/
def Pool.spawn (p : Pool α cap) (x : α) : Pool α cap :=
  match p.lifo with
  | none   => { p with lifo := some x, pushed := p.pushed + 1 }
  | some y => { (p.toRing y) with lifo := some x, pushed := p.pushed + 1 }

/-! ### Agreement with the specification

The obligations of `interface.md` §6 that this file owns, stated against `toModel`: the accounting, a tick,
and the two operations that place work — each for the full ring as much as for one with room. What makes the
full cases go through is `keepFirst_toList`: the eviction is the model's halving of the ghost view rather than
a rearrangement free to disagree with it. -/

/-- **The accounting agrees.** `inFlight` reads the container's `size`; the model reads its list's length.
`toList_length` is what makes those the same quantity rather than two counters that happen to move together. -/
theorem toModel_inFlight (p : Pool α cap) : p.inFlight = p.toModel.inFlight := by
  unfold Pool.inFlight Pool.toModel Model.Pool.inFlight
  rw [toList_length]

/-- A tick refreshes the allowance on both sides. -/
theorem toModel_tick (p : Pool α cap) : (p.tick).toModel = (p.toModel).tick := by
  simp [Pool.tick, Pool.toModel, Model.Pool.tick]


/-- **Placement commutes with the specification, room or not.**

With room, both sides append at the back and `push_toList` is the whole of the ring's part. The full ring is
the case that needs a container move: the newer half is shed *by index* — `Ring.keepFirst`, which moves the
live count and copies nothing — so the halves the implementation keeps and moves are the model's own `take`
and `drop` of its list. That is what makes the eviction a *move* of the newer half to `inject` rather than a
rearrangement free to disagree with the model about which half crosses.

`cap` must be positive: at `cap = 0` the ring is always full and `push` would write out of bounds while the
model still appended, so the two would genuinely differ. -/
theorem toModel_toRing (p : Pool α cap) (x : α) (hw : p.ring.WF) (hcap : 0 < cap) :
    (p.toRing x).toModel = (p.toModel).toRing x := by
  have hlen := toList_length p.ring
  by_cases hroom : p.ring.size < cap
  · -- The model's room test reads its own ring's length and its own `cap`; `hlen` and `hroom` are what make
    -- those the implementation's `size` and `cap`, so `simp` discharges it without being told.
    simp [Pool.toRing, Pool.toModel, Model.Pool.toRing, hroom, hlen,
          push_toList p.ring x hw hroom]
  · -- Full: shed the newer half by index, so both halves are the model's own `take` and `drop`.
    have hle : p.ring.size ≤ cap := hw.2.1
    have hsize : p.ring.size = cap := by omega
    have hhalf_le : p.ring.size / 2 ≤ p.ring.size := Nat.div_le_self _ _
    have hhalf_lt : p.ring.size / 2 < cap := by
      rw [hsize]; exact Nat.div_lt_self hcap (by decide)
    -- The kept half, read by index: the container moves its live count and copies nothing.
    have hkeep : (p.ring.keepFirst (p.ring.size / 2)).toList
        = p.ring.toList.take (p.ring.size / 2) := by
      rw [keepFirst_toList, Nat.min_eq_left hhalf_le]
    have hwf : (p.ring.keepFirst (p.ring.size / 2)).WF := keepFirst_wf p.ring (p.ring.size / 2) hw
    have hroom2 : (p.ring.keepFirst (p.ring.size / 2)).size < cap := by
      simp only [Ring.keepFirst]
      omega
    -- …and the new task appends to it, which is the model's own `take` plus the task.
    have hring : ((p.ring.keepFirst (p.ring.size / 2)).push x).toList
        = p.ring.toList.take (p.ring.size / 2) ++ [x] :=
      (push_toList (p.ring.keepFirst (p.ring.size / 2)) x hwf hroom2).trans
        (congrArg (fun l : List α => l ++ [x]) hkeep)
    simp [Pool.toRing, Pool.toModel, Model.Pool.toRing, hroom, hlen]
    -- What is left is the eviction's two fields, with `simp` having already seen that the dropped half in
    -- `inject` is the same list on both sides.
    first
      | exact hring
      | exact ⟨hring, rfl⟩

/-- **Submission agrees, full ring included.** `submit` is the placement rule plus its count, and the count
is the same on both sides, so this is `toModel_toRing` with one field moved. -/
theorem toModel_submit (p : Pool α cap) (x : α) (hw : p.ring.WF) (hcap : 0 < cap) :
    (p.submit x).toModel = (p.toModel).submit x := by
  have hstep : (p.submit x).toModel = { (p.toRing x).toModel with pushed := p.pushed + 1 } := rfl
  rw [hstep, Model.Pool.submit, ← toModel_toRing p x hw hcap]
  rfl

/-- **Spawning agrees, full ring included.** Both sides write the slot, and the task the spawn displaces
takes the same placement path — `toModel_toRing` is what carries it across, for a full ring as much as for an
empty one. -/
theorem toModel_spawn (p : Pool α cap) (x : α) (hw : p.ring.WF) (hcap : 0 < cap) :
    (p.spawn x).toModel = (p.toModel).spawn x := by
  cases h : p.lifo with
  | none =>
    simp [Pool.spawn, h, Pool.toModel, Model.Pool.spawn]
  | some y =>
    -- Both sides write the slot the same way, so the only field that differs is the ring, and the displaced
    -- task is the room case: rewriting it across the projection leaves two record literals over the same
    -- state, which is definitional.
    have hl : (p.toModel).lifo = some y := by simp [Pool.toModel, h]
    unfold Pool.spawn Model.Pool.spawn
    rw [h, hl]
    simp only []
    rw [show (p.toModel).toRing y = (p.toRing y).toModel from (toModel_toRing p y hw hcap).symm]
    -- …and `toModel` reads that state field by field, so the two sides are the same value.
    rfl

/-! ### The count companions

`Aligned` relates the scheduler's work count to `inFlight`, so what the executor's transactions need from the
pool is not where an item came from but that the count moved by exactly one. These are those statements, for
the three ways the pool's own count moves. -/

/-- The placement rule writes the ring and `inject`, and nothing else: a field it does not write reads
through it unchanged. -/
theorem toRing_lifo (p : Pool α cap) (x : α) : (p.toRing x).lifo = p.lifo := by
  unfold Pool.toRing
  split <;> rfl

/-- **Placement holds one more item.** With room the ring appends; when full it moves the newer half to
`inject` and appends. Either way exactly one more is held, because the eviction is a *move*.

The arithmetic is done on the specification's side, where the ring is a list: this is `toModel_inFlight`
twice and `toModel_toRing`, which is why the full ring needs nothing more here than that placement
law already gives. -/
theorem toRing_inFlight (p : Pool α cap) (x : α) (hw : p.ring.WF) (hcap : 0 < cap) :
    (p.toRing x).inFlight = p.inFlight + 1 := by
  rw [toModel_inFlight p, toModel_inFlight (p.toRing x), toModel_toRing p x hw hcap]
  exact Model.toRing_inFlight (p.toModel) x

/-- **A take off the ring-or-inject path holds one fewer item.** Whichever arm serves it removes exactly
one, from the ring or from `inject` — the `none` arm is the one that had nothing to remove. -/
theorem takeFromRing_inFlight (p : Pool α cap) (hw : p.ring.WF)
    (h : (p.takeFromRing).1.isSome) : (p.takeFromRing).2.inFlight + 1 = p.inFlight := by
  unfold Pool.takeFromRing at h ⊢
  cases hp : p.ring.pop with
  | mk a b =>
    cases a with
    | some x =>
      have hpos : 0 < p.ring.size := by
        have hsome : (p.ring.pop).1.isSome := by rw [hp]; rfl
        exact pop_isSome_size hsome
      have hps : b.size + 1 = p.ring.size := by
        have h := pop_size p.ring hw hpos
        rw [hp] at h
        exact h
      simp only [Pool.inFlight]
      omega
    | none =>
      cases hi : p.inject with
      | cons y rest =>
        have hlen : p.inject.length = rest.length + 1 := by simp [hi]
        simp only [Pool.inFlight]
        omega
      | nil =>
        -- The ring was empty and `inject` too, so there was nothing for the take to return.
        have hcontra : ¬ (p.takeFromRing).1.isSome := by simp [Pool.takeFromRing, hp, hi]
        exact absurd h hcontra

omit [Inhabited α] in
/-- The flush moves the slot's task into `inject` and changes nothing else — a move, so the count is the
same. It is only true when the slot really held that task. -/
theorem flush_inFlight {p : Pool α cap} {x : α} (hl : p.lifo = some x) :
    ({ p with lifo := none, inject := p.inject ++ [x] } : Pool α cap).inFlight = p.inFlight := by
  simp_all [Pool.inFlight]
  omega

/-- **A reported take holds one fewer item**, whichever way the decision went: the slot arm removes the
slot's task, the queue arms remove one from the ring or `inject`, and the flush moves the slot's task into
`inject` first — a move, so it changes nothing. -/
theorem takeReport_inFlight (p : Pool α cap) (hw : p.ring.WF) (h : (p.takeReport).item.isSome) :
    (p.takeReport).pool.inFlight + 1 = p.inFlight := by
  by_cases hpolls : p.lifoPolls < p.lifoCap
  · cases hl : p.lifo with
    | some x =>
      simp [Pool.takeReport, Pool.inFlight, hpolls, hl]
      omega
    | none =>
      have h' : (p.takeFromRing).1.isSome := by simpa [Pool.takeReport, hpolls, hl] using h
      simpa [Pool.takeReport, Pool.inFlight, hpolls, hl] using takeFromRing_inFlight p hw h'
  · cases hl : p.lifo with
    | some x =>
      -- The allowance is spent with the slot occupied: the slot moves to `inject` (the count is unchanged)
      -- and then the ring-or-inject take removes one. Which pool that is gets identified once, rather than
      -- unfolded into the arithmetic.
      have h' : (({ p with lifo := none, inject := p.inject ++ [x] } : Pool α cap).takeFromRing).1.isSome := by
        simpa [Pool.takeReport, hpolls, hl] using h
      have hc := takeFromRing_inFlight ({ p with lifo := none, inject := p.inject ++ [x] } : Pool α cap) hw h'
      have hf := flush_inFlight (p := p) hl
      have hgoal : (p.takeReport).pool
          = ({ p with lifo := none, inject := p.inject ++ [x] } : Pool α cap).takeFromRing.2 := by
        simp [Pool.takeReport, hpolls, hl]
      rw [hgoal]
      omega
    | none =>
      have h' : (p.takeFromRing).1.isSome := by simpa [Pool.takeReport, hpolls, hl] using h
      have hgoal : (p.takeReport).pool = (p.takeFromRing).2 := by
        simp [Pool.takeReport, hpolls, hl]
      rw [hgoal]
      exact takeFromRing_inFlight p hw h'

/-- **Submission holds one more item**, full ring included. -/
theorem inFlight_submit (p : Pool α cap) (x : α) (hw : p.ring.WF) (hcap : 0 < cap) :
    (p.submit x).inFlight = p.inFlight + 1 := by
  have h : (p.submit x).inFlight = (p.toRing x).inFlight := rfl
  rw [h, toRing_inFlight p x hw hcap]

/-- **A spawn holds one more item.** The slot is written either way, and the task it displaced is placed
rather than dropped. -/
theorem spawn_inFlight (p : Pool α cap) (x : α) (hw : p.ring.WF) (hcap : 0 < cap) :
    (p.spawn x).inFlight = p.inFlight + 1 := by
  cases hl : p.lifo with
  | none =>
    simp [Pool.spawn, Pool.inFlight, hl]
    omega
  | some y =>
    have hring := toRing_inFlight p y hw hcap
    simp [Pool.spawn, Pool.inFlight, hl, toRing_lifo] at hring ⊢
    omega

end LeanIn.Sched
