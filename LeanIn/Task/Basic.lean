import Std
import LeanIn.Sched.Executor

/-!
# The task layer

`docs/interface.md` §4: our own `Task`/`Async`, because `Std.Async` cannot be reused — it is
`BaseIO (MaybeTask α)` and every operation delegates to `Task`, so it cannot be driven on one carrier.

Three pieces:

* `Item` is what the executor holds: one step of some computation, ready to run.
* `Async α` is a **scheduleable computation**, in continuation-passing style: `step k resume` runs it until it
  either finishes — calling `k` — or reaches something it must wait for, in which case it registers a
  continuation and returns. It never blocks the thread, which is what makes a single carrier enough.
* `Task α` is the **handle**: the cell its value lands in, and where an awaiter leaves its continuation.

`resume` is *how to schedule*, and it is one function for two jobs: continuing a computation that yielded, and
starting a child. That is why this layer needs no executor of its own — the runtime supplies the function and
decides whether scheduling means the local slot or the shared queue.

**Awaiting is the O3 seam turned inward.** An external event is "attach a continuation that pushes into the
queue and notifies"; here the event is our own task finishing, and the continuation an awaiter leaves is pushed
back onto the executor the same way. So there is one path, whether the completer is this task, another task, or
a stock `Task` on a pool worker — and that path never runs anything on the completing thread.

**The name collides with core's `Task`, but only inside this library.** `LeanIn.Task` shadows `_root_.Task` for
files under `LeanIn/`, so code in this tree that wants the stock one — `IO.asTask`'s `Task.Priority.dedicated`
in the test clients — spells it `_root_.Task`. The interface names these two types, so the collision comes with
the interface rather than from the layout.
-/

namespace LeanIn.Task

/-- **One unit of scheduled work**: a step of some computation, ready to run. Named rather than a bare
`IO Unit` so that the executor's item type has an `Inhabited` instance, which the pool's ghost view needs. -/
structure Item where
  /-- Run this step. -/
  run : IO Unit

instance : Inhabited Item := ⟨⟨pure ()⟩⟩

/-- **The join cell**: what a handle is. The value once there is one, and the continuations left by whoever
awaited it before then.

One lock, because the resolver and the awaiter can be different threads — and here they usually are: the
resolver is whoever finished the task, the awaiter is a carrier that yielded. -/
structure Join (α : Type) where
  lock : Std.Mutex (Option α × List (α → IO Unit))

def Join.new : IO (Join α) := return ⟨← Std.Mutex.new (none, [])⟩

/-- **Resolve**, running whoever was waiting.

Inside the lock the value goes in and the waiting continuations come out; outside it they run. Running them
inside would mean enqueuing — which takes the executor's lock — while holding this one, and two locks in one
path is how a runtime acquires a lock order nobody chose.

Resolving twice is a defect rather than a race to be tolerated, so it is loud: a handle is resolved by the one
computation that owns it, exactly once, and a second resolution means two writers. -/
def Join.resolve (j : Join α) (v : α) : IO Unit := do
  let ks ← j.lock.atomically do
    let st ← get
    match st.1 with
    | some _ => throw (IO.userError "Join.resolve: a task was resolved twice")
    | none   => set (some v, ([] : List (α → IO Unit))); return st.2
  for k in ks do k v

/-- **Register, or run now.** An awaiter that arrives after the value did must not be left waiting: it runs
immediately, which is also what makes awaiting a finished handle return at once instead of yielding. -/
def Join.onReady (j : Join α) (k : α → IO Unit) : IO Unit := do
  let now? ← j.lock.atomically do
    let st ← get
    match st.1 with
    | some v => return some v
    | none   => set (st.1, st.2 ++ [k]); return none
  match now? with
  | some v => k v
  | none   => pure ()

/-- **A scheduleable computation.**

`step k resume` runs the computation until it finishes, calling `k` with the value, or until it must wait, in
which case it registers a continuation and returns. `bind` composes the continuations, so a resumed
computation continues from where it yielded rather than from its beginning — the difference between this and a
bare `Job`, which is a value that must be re-run.

`resume` is `BaseIO` rather than `IO`, and that is the O3 seam showing through: the one place a schedule call
has to happen is *inside a waker* — a continuation registered on a stock `Task`, running on a pool worker —
and a waker cannot call `IO`. Enqueuing takes a lock and notifies a condvar, so `BaseIO` is all it needs, and
the runtime's `resumeOf` is that function. -/
structure Async (α : Type) where
  step : (α → IO Unit) → (Item → BaseIO Unit) → IO Unit

instance : Inhabited (Async α) := ⟨⟨fun _ _ => pure ()⟩⟩

instance : Monad Async where
  pure v   := ⟨fun k _ => k v⟩
  bind a f := ⟨fun k resume => a.step (fun v => (f v).step k resume) resume⟩

/-- Run an `IO` action as a step of a computation. This is the inside of `interface.md` §4's one bridge: a leaf
operation — a timer, a socket, a stock `Task` — arrives as an action, and what keeps it non-blocking is that
whoever completes it schedules the continuation instead of running it here. -/
def Async.ofIO (act : IO α) : Async α := ⟨fun k _ => do k (← act)⟩

instance : MonadLift IO Async where monadLift act := Async.ofIO act

/-- **A handle** on a spawned computation: the cell its value lands in. -/
structure Task (α : Type) where
  cell : Join α

/-- **Start a computation on the current worker.** The child's first step is enqueued through `resume`, which
is the local route, so a chain of spawns stays on the core its parent ran on. -/
def Async.spawn (a : Async α) : Async (Task α) := ⟨fun k resume => do
  let cell ← Join.new
  resume ⟨a.step (fun v => Join.resolve cell v) resume⟩
  k ⟨cell⟩⟩

/-- **The value, if it is already there.** -/
def Join.value? (j : Join α) : IO (Option α) := j.lock.atomically do return (← get).1

/-- **Await.** If the value is already there, `k` is called now and the step does not yield: awaiting a
finished handle costs a lock and no scheduling round, which is what a `JoinHandle` polled as ready does.
Otherwise the continuation left behind *schedules itself* when the value arrives, and `step` returns without
calling `k`.

Reading then registering is not a race: if the value arrives between the two, `onReady` runs the continuation
immediately, which is the case it exists for. -/
def Async.await (t : Task α) : Async α := ⟨fun k resume => do
  match ← t.cell.value? with
  | some v => k v
  | none   => Join.onReady t.cell (fun v => resume ⟨k v⟩)⟩

/-- **What generic code is written against**: joining and starting, with the handle type alongside. -/
class MonadAwait (m : Type → Type) where
  /-- The handle type: what starting a computation in `m` gives you. -/
  Handle : Type → Type
  /-- Wait for a handle's value. -/
  await : Handle α → m α

/-- Anything that can also start computations. -/
class MonadAsync (m : Type → Type) extends MonadAwait m where
  /-- Start a computation on the current worker. -/
  spawn : m α → m (Handle α)

instance : MonadAwait Async where
  Handle := Task
  await  := Async.await

instance : MonadAsync Async where
  spawn := Async.spawn

/-- Run both and return both values. Concurrent in the sense that matters: both are scheduled before either is
awaited. Written once, against the class, so any implementation of it gets this for free. -/
def concurrently [Monad m] [MonadAsync m] (a b : m α) : m (α × α) := do
  let ha ← MonadAsync.spawn a
  let hb ← MonadAsync.spawn b
  let va ← MonadAwait.await ha
  let vb ← MonadAwait.await hb
  return (va, vb)

/-- Run it and drop the handle: still scheduled, nothing waits for it. -/
def background [Monad m] [MonadAsync m] (a : m α) : m Unit := do
  let _ ← MonadAsync.spawn a
  return ()

end LeanIn.Task
