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

/-- The owner's take.

The LIFO slot is preferred while the tick's allowance lasts; **when the allowance runs out with a task
still in the slot, the slot is flushed to `inject` before the ring is consulted**, so the allowance cannot
strand it. -/
def Pool.take (p : Pool α cap) : Option α × Pool α cap :=
  if p.lifoPolls < p.lifoCap then
    match p.lifo with
    | some x => (some x, { p with lifo := none, lifoPolls := p.lifoPolls + 1, taken := p.taken + 1 })
    | none   => p.takeFromRing
  else
    match p.lifo with
    | some x => ({ p with lifo := none, inject := p.inject ++ [x] }).takeFromRing
    | none   => p.takeFromRing

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

/-- **Submit, with overflow.** Append at the back if there is room. Otherwise the *newer* half leaves for
`inject` and the *older* half stays with the new task — see `Model.Pool.submit`, where the reason is that
intake places work in the first half, so anything found in the second is provably not freshly intaken. -/
def Pool.submit (p : Pool α cap) (x : α) : Pool α cap :=
  if p.ring.size < cap then
    { p with ring := p.ring.push x, pushed := p.pushed + 1 }
  else
    let half := p.ring.size / 2
    let drained := p.ring.drain
    let keep := drained.1.take half
    let evict := drained.1.drop half
    let refilled := keep.foldl (fun (r : Ring α cap) y => r.push y) (emptyRing α cap)
    { p with ring   := refilled.push x,
             inject := p.inject ++ evict,
             pushed := p.pushed + 1 }

end LeanIn.Sched
