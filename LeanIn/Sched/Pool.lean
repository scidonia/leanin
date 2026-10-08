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
produces the executor's records lives with the client. What *is* owed and stated where it is owed: the
commutation fact for the overflow, which needs a drain-and-refill lemma this container does not yet have,
and is therefore carried as an example rather than a theorem.
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

/-- Drain the ring's live elements, oldest first. The container can only pop the front, so evicting the
**newer** half of a full ring means reading them all out and pushing the older half back. -/
def _root_.LeanIn.Ring.drain (r : Ring α cap) : List α × Ring α cap :=
  (List.range r.size).foldl
    (fun (acc : List α × Ring α cap) _ =>
      match acc.2.pop with
      | (some x, r') => (acc.1 ++ [x], r')
      | (none, _)    => acc)
    ([], r)

/-- **Where a task goes when it joins the ring** — the implementation's `Model.Pool.toRing`. Append at the
back if there is room. Otherwise the *newer* half leaves for `inject` and the *older* half stays with the new
task: intake places work in the first half, so anything found in the second is provably not freshly intaken.

Factored out so `spawn` places the task its LIFO slot displaces by the same rule, and there is one overflow
rather than two that can drift. It does not count: the task was counted when it entered the pool. -/
def Pool.toRing (p : Pool α cap) (x : α) : Pool α cap :=
  if p.ring.size < cap then
    { p with ring := p.ring.push x }
  else
    let half := p.ring.size / 2
    let drained := p.ring.drain
    let keep := drained.1.take half
    let evict := drained.1.drop half
    let refilled := keep.foldl (fun (r : Ring α cap) y => r.push y) (emptyRing α cap)
    { p with ring   := refilled.push x,
             inject := p.inject ++ evict }

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

The first three obligations of `interface.md` §6's refinement, stated against `toModel`. The overflow's
commutation is not here: it is stated over `Ring.drain`'s read-out-and-refill, and the lemma tying that to
`take`/`drop` does not exist yet. -/

/-- **The accounting agrees.** `inFlight` reads the container's `size`; the model reads its list's length.
`toList_length` is what makes those the same quantity rather than two counters that happen to move together. -/
theorem toModel_inFlight (p : Pool α cap) : p.inFlight = p.toModel.inFlight := by
  unfold Pool.inFlight Pool.toModel Model.Pool.inFlight
  rw [toList_length]

/-- A tick refreshes the allowance on both sides. -/
theorem toModel_tick (p : Pool α cap) : (p.tick).toModel = (p.toModel).tick := by
  simp [Pool.tick, Pool.toModel, Model.Pool.tick]

omit [Inhabited α] in
/-- **Submission with room holds one more item.** `Ring.push` moves `size` and nothing else, so the
accounting follows without any invariant — no `Consistent` hypothesis, because nothing is *removed*. -/
theorem inFlight_submit_of_room (p : Pool α cap) (x : α) (hroom : p.ring.size < cap) :
    (p.submit x).inFlight = p.inFlight + 1 := by
  by_cases h : p.ring.size < cap
  · simp only [Pool.submit, Pool.toRing, ite_eq_left h, Pool.inFlight, Ring.push]
    omega
  · exact absurd hroom h


/-- **Placement agrees, while the ring has room.** Both sides append the task at the back of the ring, and
`push_toList` is the whole of the ring's part. The full ring is the owed drain-and-refill lemma named above;
this case deliberately does not need it. -/
theorem toModel_toRing_of_room (p : Pool α cap) (x : α)
    (hw : p.ring.WF) (hroom : p.ring.size < cap) :
    (p.toRing x).toModel = (p.toModel).toRing x := by
  have hlen := toList_length p.ring
  -- The model's room test reads its own ring's length and its own `cap`; `hlen` and `hroom` are what make
  -- those the implementation's `size` and `cap`, so `simp` discharges it without being told.
  simp [Pool.toRing, Pool.toModel, Model.Pool.toRing,
        hroom, hlen, push_toList p.ring x hw hroom]

/-- **Submission with room.** The ring has space, so both sides append at the back and count the push.
This is the `Impl.push ⊑ Model.push` case that needs no eviction. -/
theorem toModel_submit_of_room (p : Pool α cap) (x : α)
    (hw : p.ring.WF) (hroom : p.ring.size < cap) :
    (p.submit x).toModel = (p.toModel).submit x := by
  have hlen := toList_length p.ring
  simp [Pool.submit, Pool.toRing, Pool.toModel, Model.Pool.submit, Model.Pool.toRing,
        hroom, hlen, push_toList p.ring x hw hroom]

/-- **Spawning agrees, while the ring has room.** Both sides write the slot, and the displaced task takes
the same placement path — `toModel_toRing_of_room` is what carries it across. The full ring is the same owed
lemma as `submit`'s overflow. -/
theorem toModel_spawn_of_room (p : Pool α cap) (x : α)
    (hw : p.ring.WF) (hroom : p.ring.size < cap) :
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
    rw [show (p.toModel).toRing y = (p.toRing y).toModel from
          (toModel_toRing_of_room p y hw hroom).symm]
    -- …and `toModel` reads that state field by field, so the two sides are the same value.
    rfl

end LeanIn.Sched
