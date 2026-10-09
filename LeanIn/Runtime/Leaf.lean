import Std
import LeanIn.Runtime.Basic
import LeanIn.Task.Error

/-!
# The leaf seam

`interface.md` §4: the leaf operations are not ours. Timers, sockets, DNS, signals and processes stay in
`Std.Async`, and they are reached across one seam — "an external event attaches a continuation that pushes into
`inject` and notifies". This file is that seam, in both directions.

**Inward** (what this file does): a leaf produced by `Std.Async` becomes something our tasks can await without
blocking. The continuation is registered on the leaf's `Task`, and all it does when it fires is *enqueue* our
resume — so nothing of ours runs on the thread that completed the work.

**`Std.Async` is referenced here and, by the boundary W1 sets, nowhere else in the tree.** Before this file the
runtime called no `Std.Async` at all; the platform library was in the build only because `Std.Internal`
re-exports it publicly. Everything outside this module stays on the C++ primitives.

## Two things the conversion cannot do

* **A failure has nowhere to go.** `interface.md` §5 has no error channel on a task, so a leaf that fails
  cannot deliver an error to its awaiter. It says so loudly rather than dropping the work and leaving the
  awaiter parked forever.
* **A continuation must be kept alive.** The `Task` that `BaseIO.bindTask` returns is the registration, and a
  dropped `Task` is a dropped continuation — this is inherited from the shape SC6's client used, and whether
  retention is strictly required is worth a test rather than an assumption. So the conversions take a registry
  the caller owns, which is also why there is no `MonadLift` instance: retention is runtime-scoped state, not
  something an instance can carry.
-/

namespace LeanIn.Runtime

/-- Where a conversion's registrations are kept alive. One per runtime is enough. -/
abbrev Hooks := IO.Ref (List (_root_.Task Unit))

def Hooks.new : IO Hooks := IO.mkRef []

/-- **How many registrations are still outstanding.** A hook stops being pending when its leaf completes — that
is when the continuation it holds runs — so this is the part of "in flight" that a model of pool items cannot
see: a task parked on a leaf holds no pool item at all, and a driver that stopped there would abandon it. Reading
it after a run returns is the conformance check that the model's invariants cannot state. -/
def pending (hooks : Hooks) : IO Nat := do
  let ts ← hooks.get
  let mut n := 0
  for t in ts do
    unless (← IO.getTaskState t) == .finished do
      n := n + 1
  return n

/-- **The step that does the work**, factored out so `awaitTask` and `awaitAsync` share one path: register a
continuation that enqueues, and return.

`resume` is the runtime's scheduling function, so the completion is delivered as fresh work on the carrier
rather than run on whatever thread completed the leaf. -/
def awaitTaskStep {α : Type} (hooks : Hooks) (t : _root_.Task (Except IO.Error α))
    (k : α → IO Unit) (resume : LeanIn.Task.Item → BaseIO Unit) : IO Unit := do
  let hooked ← BaseIO.bindTask t (fun r => do
    match r with
    | Except.ok v    => resume ⟨k v⟩
    | Except.error e => panic! s!"awaitTask: the awaited task failed: {e}"
    return _root_.Task.pure ())
  hooks.modify (· ++ [hooked])

/-- **Wait for a stock `Task`** without blocking. -/
def awaitTask {α : Type} (hooks : Hooks) (t : _root_.Task (Except IO.Error α)) : LeanIn.Task.Async α :=
  ⟨fun k resume => awaitTaskStep hooks t k resume⟩

/-- **Wait for a promise's result** — the shape `Std.Async`'s leaves resolve, since `Async.sleep` and its
relatives are `ofPurePromise` over the reactor. -/
def awaitPromise {α : Type} (hooks : Hooks) (p : IO.Promise (Except IO.Error α)) : LeanIn.Task.Async α :=
  awaitTask hooks (Std.Async.AsyncTask.ofPromise p)

/-- **Any `Std.Async` computation as one of ours.** `Async α` is `BaseIO (MaybeTask (Except IO.Error α))`: run
it, and if it hands back a `Task`, register our resume on it. -/
def awaitAsync {α : Type} (hooks : Hooks) (a : Std.Async.Async α) : LeanIn.Task.Async α :=
  ⟨fun k resume => do
    let mt ← Std.Async.BaseAsync.toRawBaseIO a
    match mt with
    | .pure (.ok v)    => k v
    | .pure (.error e) => panic! s!"awaitAsync: the computation failed: {e}"
    | .ofTask t        => awaitTaskStep hooks t k resume⟩

/-- **Wait for a stock `Task`, carrying its failure.** The sibling of `awaitTask`, and the difference is the whole
point of `EAsync`: where that one says a failure has nowhere to go and panics, this returns it — which is what a
socket needs, because a client that goes away mid-request is an ordinary event rather than a defect.

The registry and the one-continuation shape are the same; only the reading of the result differs. -/
def awaitTaskE {α : Type} (hooks : Hooks) (t : _root_.Task (Except IO.Error α)) : Task.EAsync IO.Error α :=
  ⟨fun k resume => do
    let hooked ← BaseIO.bindTask t (fun r => do resume ⟨k r⟩; return _root_.Task.pure ())
    hooks.modify (· ++ [hooked])⟩

/-- **Wait for a promise's result, carrying its failure.** -/
def awaitPromiseE {α : Type} (hooks : Hooks) (p : IO.Promise (Except IO.Error α)) : Task.EAsync IO.Error α :=
  awaitTaskE hooks (Std.Async.AsyncTask.ofPromise p)

/-- **Any `Std.Async` computation, carrying its failure.** -/
def awaitAsyncE {α : Type} (hooks : Hooks) (a : Std.Async.Async α) : Task.EAsync IO.Error α :=
  ⟨fun k resume => do
    let mt ← Std.Async.BaseAsync.toRawBaseIO a
    match mt with
    | .pure r   => k r
    | .ofTask t => (awaitTaskE hooks t).step k resume⟩

end LeanIn.Runtime
