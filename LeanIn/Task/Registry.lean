import Std
import LeanIn.Task.Basic

/-!
# A `JoinSet`-shaped set of handles

`docs/interface.md` §4: a set of spawned computations that can be awaited as a group and drained, without the
caller threading a `List` of handles through every recursion. It is task-layer code like `Sync.lean`, because its
members are computations and its operations are steps of computations; it holds no executor state and no leaf
registration, so `Runtime.pending` does not count a registered handle.

**Membership is a `List` under one `Std.Mutex`, and the registry is unbounded.** A `JoinSet` holds handles; it
does not meter admissions. The connection limit already lives in the caller's `Task.Sync.Semaphore` at the accept
boundary — `serveBounded` takes a permit before `Listener.accept`, and that permit is what `Service.Bounded` is
proved against — so a second bound inside the registry would be a second place the limit lives, and it would make
`add` a parking operation, which is wrong for a drain path. Tokio makes the same split.

**No operation awaits inside a critical section.** Every case is pure list code over one `Std.Mutex`; the awaits
happen *outside* the lock, on a snapshot the lock has released. This is `Join.resolve`'s rule
(`LeanIn/Task/Basic.lean`: running the continuations inside would enqueue — which takes the executor's lock —
while holding this one) restated for a registry, and it is also why no `Async` is ever called under `atomically`.
An `await` under the lock would wedge the single carrier: the continuation it enqueues could never be taken while
this step still holds the lock.

**The registry holds handles, not ownership.** Dropping it aborts nothing — Lean has no drop hook that could
(W5: drop-driven cancellation is a stated non-goal), and a `Task` is a value whose cell is the value's home, so a
handle the registry took is still awaitable by anyone else holding it. `drain` does not cancel; cancelling what it
holds is `Task.cancel`/`Runtime.cancel`, issued by whoever holds the clock.

**Two propositions, argued rather than proved.** `Registry.Sound`: what the registry still holds plus what it has
drained accounts for what was added — `held.length + drained.length = added.length` at quiescent points, under the
discipline that every `add` is followed by exactly one `drain`-take — and no handle is awaited twice. It holds by
construction on one carrier: `held` is the single `Std.Mutex`-guarded list below, whose `add` and take are each a
single critical section, and on one carrier steps do not interleave, so the accounting is a list lemma about a
cons and a take rather than a property of concurrent state. `Local.Inherited`: a spawned child's context is its
parent's local — the one line `«local» := ctx.«local»` in `Async.spawn` (`Task/Basic.lean`) — so `Async.local` read
by a child is the innermost enclosing `withLocal` value at its spawn site. It too holds by construction: `spawn`
copies `ctx.«local»` into the child and every continuation closes over the `Ctx` that built it, so the value is
the termination rule of the term, not runtime state any step has to inspect. Both are **argued, not proved**: no
refinement theorem links the code to a model (`docs/primitive-theory.md` §4), so the argument is the whole of
what is claimed here, and SC15 is its executable half.

**The liveness half of `Registry.Sound` is named and not claimed.** That a `drain` *terminates* is not derivable
from the available axioms: a handler that neither finishes nor is cancelled leaves its `await` parked forever, so
the drain is unbounded — exactly as `shutdownAndWait`'s wait is unbounded (`Blocking.lean`). This is the part of
the proposition no argument on these axioms closes, stated rather than omitted. -/

namespace LeanIn.Task

/-- **A set of handles.** One lock over the membership list, so `add` and a take are single critical sections and
no reader ever sees a half-updated set. -/
structure Registry (α : Type) where
  /-- The handles currently registered, newest first (the registry promises no order). -/
  state : Std.Mutex (List (Task α))

/-- An empty registry. -/
def Registry.new : IO (Registry α) :=
  return ⟨← Std.Mutex.new ([] : List (Task α))⟩

/-- **Register a handle.** One critical section, a cons under the lock; there is nothing to release and so nothing
to await. A cons, not an append, because the registry has no specified order — a `JoinSet` promises none, and no
clause of SC15 reads it — so the newest handle at the head is the whole of the shape, and O(1) rather than the
O(queue length) an append costs in a serving path. -/
def Registry.add (r : Registry α) (h : Task α) : IO Unit :=
  r.state.atomically do set (h :: (← get))

/-- **Spawn and register in one step.** The handle is added as soon as the spawn's step runs, so a caller that
holds the registry has it without a second bookkeeping step of its own. -/
def Registry.spawn (r : Registry α) (a : Async α) : Async (Task α) := do
  let h ← Async.spawn a
  monadLift (r.add h)
  return h

/-- **How many handles are registered.** The list's length, read under the lock. -/
def Registry.size (r : Registry α) : IO Nat :=
  r.state.atomically do return (← get).length

/-- **Await every registered handle, keeping them registered.** The membership is snapshotted under the lock and
released, then each handle is awaited in turn *outside* it. A handle that was already resolved costs no scheduling
round (`Async.await`'s "already there" path), and the registry keeps its list so a later `size` or `joinAll`
still sees it. -/
def Registry.joinAll (r : Registry α) : Async Unit := do
  let hs ← monadLift (r.state.atomically (do return (← get)) : IO (List (Task α)))
  for h in hs do
    let _ ← Async.await h
  return ()

/-- **Take the whole membership, clear the registry, and await every handle taken.** One critical section takes
the list and leaves the registry empty; the take is what makes a drain a registry operation rather than a caller's
`List.forM`. The taken handles are then awaited *outside* the lock, in the step that took them.

The await is what makes the drain's return mean the handlers finished: a drain that took the handles and dropped
them would report a return the handlers had not earned. Awaiting costs nothing extra for a handle already
resolved — `Async.await`'s "already there" path runs the continuation in this step without a scheduling round —
and a handle whose computation was cancelled has its cell resolved by `Task.cancel` through `Join.resolveFirst`,
so awaiting it takes that same "already there" path rather than parking. A handler that neither finishes nor is
cancelled makes the drain unbounded; that liveness gap is stated in `docs/decisions.md` D16, as
`shutdownAndWait`'s unbounded wait is stated in `Blocking.lean`. -/
def Registry.drain (r : Registry α) : Async Unit := do
  let hs ← monadLift (r.state.atomically (do
    let hs ← get
    set ([] : List (Task α))
    return hs) : IO (List (Task α)))
  for h in hs do
    let _ ← Async.await h
  return ()

end LeanIn.Task
