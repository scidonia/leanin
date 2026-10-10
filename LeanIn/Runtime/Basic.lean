import Std
import LeanIn.Task.Basic

/-!
# The single-carrier runtime

`interface.md` §3's `blockOn` and §4's task layer wired to `Sched.Executor`: the executor holds `Item`s, the
caller drives them on its own thread, and nothing is handed to a pool worker.

The one scheduling function this file owns is `resumeOf`, and it is where `interface.md` §3's rule lives: a
step that yields re-schedules itself and a `spawn` inside a body schedules its child, both **locally** — the
executor's LIFO slot — so a chain stays on the core its parent ran on. A spawn from *outside* a body has no
slot to use and takes the ring instead, which is the other half of the same rule.

No worker threads, no pool: an item is taken and run on the caller, and `Executor.work` parks that thread when
nothing is ready — which is exactly why a completion arriving from another thread may only *enqueue*.
-/

namespace LeanIn.Runtime

/-- The runtime's executor: it holds task steps. -/
abbrev Executor (cap : Nat) := Sched.Executor Task.Item cap

/-- **How an item schedules**: enqueue a step on the current worker, the local route. `BaseIO`, because this
is the function a waker calls — see `Task.Async`. -/
def resumeOf (e : Executor cap) : Task.Item → BaseIO Unit := fun it => e.spawnBase it

/-- **Where a spawn asks the executor to place the task's first step.** `.high` is the owner-local one-slot LIFO
buffer, served before the ring while the tick's allowance lasts; `.normal` is the FIFO ring. It is a placement
request and promises nothing about *when* the task runs. -/
inductive Priority where
  | high
  | normal

/-- **Spawn from outside a body**: the ring, because there is no current worker's slot to use — the interface's
"or inject if called from outside". `prio` selects the placement lane: `.high` goes to the LIFO slot
(`Executor.spawnBase`), `.normal` appends to the ring (`Executor.submitBase`); a `.high` task is served sooner,
never promised to run. -/
def spawn (e : Executor cap) (prio : Priority) (a : Task.Async α) : IO (Task.Task α) := do
  let cell ← Task.Join.new
  let cancel ← Task.Cancel.new
  let ctx : Task.Ctx := { cancel := cancel, resume := fun it => resumeOf e (it.stamp cancel), «local» := {} }
  let it := Task.Item.stamp (Task.Item.ofAction (a.step (fun v => Task.Join.resolve cell v) ctx)) cancel
  match prio with
  | .high   => e.spawnBase it
  | .normal => e.submitBase it
  return ⟨cell, cancel⟩

/-- **The counters a handle reports.**

`ready` and `parked` are the model projection's own two numbers, read through `Executor.observe` — the
`Scheduler.toModel` half of `State.toModel`, the same projection the refinement's scheduler obligations are
stated over, so a counter cannot disagree with the model about what the executor holds. `carriers` is per
carrier, index 0 while there is one carrier, and `some` only for an executor built metered. -/
structure Metrics where
  /-- Work ready to be taken: the model projection's `work`, which `State.Aligned` proves equals the pool's
  `inFlight`. -/
  ready    : Nat
  /-- Carriers parked now: the model projection's `parked`. -/
  parked   : Nat
  /-- Per-carrier counters, `some` only for a metered executor. -/
  carriers : Option (List Sched.CarrierCounters)
deriving Repr

/-- **The capability handed to a thread that is not a carrier.**

It holds the executor and exposes exactly three operations — `spawn`, `stop`, `metrics` — and the withheld half
is the point: `Executor.work`, `Executor.park`, `Executor.tryTake`, `Executor.snapshot` and every `Hooks`
operation are carrier-side and are not reachable from here.

What makes it usable off-carrier is that every shared cell those three operations reach is read and written
inside that cell's own lock, so their critical sections are serializable against a carrier's and the executor's
`State.Aligned`/`Scheduler.Live` invariants survive a foreign-thread spawn; and a spawn from a parked-against
thread cannot be lost, because `submitBase`'s notify is issued inside the same lock the parking predicate is
re-checked under. That is an argument, not a theorem — it needs the serializability lemma
`docs/primitive-theory.md` §4 states as unproved — and it is not a `Send` marker: it fixes one object by audit
and checks nothing a caller shares with a thread. -/
structure Handle (α : Type) (cap : Nat) where
  private mk ::
    /-- The executor the handle holds. Both this field and the constructor are **private**, so the three
    operations below are the whole surface rather than a convention: a caller holding a `Handle` can neither
    project the executor out nor build one, and so cannot reach the carrier-side operations — `work`, `park`,
    `tryTake`, `snapshot` — that the handle exists to withhold. -/
    private e : Sched.Executor α cap

/-- The handle for an executor. -/
def handle (e : Sched.Executor α cap) : Handle α cap := ⟨e⟩

/-- **Spawn from a thread that is not a carrier.** The handle must be one over a task executor — the runtime's
only executor, whose items are steps — because the child's first step is what it enqueues; the item it builds
carries the child's completion cell and the child's token, and `prio` is the placement lane the caller asks
for. -/
def Handle.spawn (h : Handle Task.Item cap) (prio : Priority) (a : Task.Async α) : IO (Task.Task α) := do
  let cell ← Task.Join.new
  let cancel ← Task.Cancel.new
  let ctx : Task.Ctx := { cancel := cancel, resume := fun it => resumeOf h.e (it.stamp cancel), «local» := {} }
  let it := Task.Item.stamp (Task.Item.ofAction (a.step (fun v => Task.Join.resolve cell v) ctx)) cancel
  match prio with
  | .high   => h.e.spawnBase it
  | .normal => h.e.submitBase it
  return ⟨cell, cancel⟩

/-- Stop the executor: `Executor.stop`, so a later iteration of a serving loop sees the flag. -/
def Handle.stop (h : Handle α cap) : IO Unit := h.e.stop

/-- The two counts and the per-carrier counters, read without mutating or notifying anything. -/
def Handle.metrics (h : Handle α cap) : IO Metrics := do
  let (ready, parked) ← h.e.observe
  let carriers ←
    if h.e.metered then
      let cs ← h.e.counters.atomically do return (← get)
      pure (some cs)
    else pure none
  return { ready, parked, carriers }

/-- **An executor that accumulates per-carrier counters.** `Executor.new` leaves metering off, so the default
item path pays one test and neither a lock nor a clock read; this is the configuration the cost rows measure. -/
def Executor.newMetered (cap workers : Nat) : IO (Executor cap) := do
  let e ← Sched.Executor.new Task.Item cap workers
  return { e with metered := true }

/-- **Drive the executor on the caller's thread** until `finished` holds, with a hook for a driver that has
somewhere to advance to.

This is the single-carrier claim as code: there is no other thread to hand the wait to, so the caller runs the
item itself and parks in `Executor.workWith` when nothing is ready. That park is the protocol's — the predicate
is re-checked under the same lock a submit notifies under — so a completion arriving while this thread is parked
wakes it rather than being lost.

`idle` reaches `Executor.workWith`, which asks it only when the pool is empty while the executor still runs, so
a driver with nothing to advance to behaves exactly as before. `now` is read around each item's run when the
executor is metered, and never otherwise. -/
def blockOnWith (e : Executor cap) (now : IO Nat) (idle : IO Bool) (finished : IO Bool) : IO Unit := do
  let mut go := true
  while go do
    if ← finished then go := false
    else
      match ← e.workWith idle with
      | some it =>
        if e.metered then
          let t0 ← now
          it.fire
          let t1 ← now
          e.accrue (t1 - t0)
        else it.fire
      | none    =>
        -- The pool is empty *and* the executor is stopping, which for a worker is the end of its shift and for
        -- the driver is not the end of anything. A stopped executor can still hold work in the form of
        -- continuations registered on leaves — those are not in the pool by construction, because an awaited
        -- leaf yields and queues nothing — so ending the driver here abandons them, and every task waiting on
        -- one hangs forever.
        --
        -- Waiting instead is the drain the model's shutdown states ("set `stopping`, notify all, drain"): a
        -- completion arrives through `resume`, which enqueues and notifies, so the wait wakes with work to take
        -- or with the value the caller is waiting for. The bound on a drain that cannot finish is a deadline,
        -- which is the caller's to impose and W7's to make cheap.
        e.state.atomicallyOnce e.cv
          (pred := do
            let st ← get
            if st.pool.inFlight ≠ 0 then return true
            else
              -- Record that the driver is about to wait, in the state the producers read. `submit` and
              -- `spawnBase` notify only when `parked ≠ 0`, so a wait that does not say so is a wait nothing will
              -- wake — which is exactly what happened here: the loop's own poll timer completed, the completion
              -- enqueued, and the driver slept on. `Executor.work`'s predicate does this; this one has to too.
              if st.sched.parked = 0 then
                set { st with sched := { st.sched with parked := 1 } }
              return false)
          (k := do
            let st ← get
            if st.sched.parked ≠ 0 then
              set { st with sched := { st.sched with parked := 0 } })

/-- **Drive the executor on the caller's thread** until `finished` holds.

`blockOnWith` with a hook that reports nothing and a clock that is never read — the driver `Runtime.run` uses,
and the one every existing scenario runs through. -/
def blockOn (e : Executor cap) (finished : IO Bool) : IO Unit :=
  blockOnWith e IO.monoNanosNow (do return false) finished

/-- Run one computation to completion on the caller's thread and return its value, driving it with `now` and
`idle`: `idle` is the driver's own step when nothing in the pool can run, which is where a virtual clock
advances.

The completion is a cell the computation's own last step writes, so the driver's stop condition is the value
arriving rather than a clock or a count. If the driver stops for another reason — the pool stopping — the
missing value is reported rather than filled in with a default. -/
def runWith (e : Executor cap) (now : IO Nat) (idle : IO Bool) (a : Task.Async α) : IO α := do
  let done ← IO.mkRef (none : Option α)
  -- The driver's own computation carries a token nothing hands out, and its first item is left unstamped: the
  -- driver is a caller's thread waiting, and the computation it drives is not one another task holds a handle to.
  let ctx : Task.Ctx := { cancel := ← Task.Cancel.new, resume := resumeOf e, «local» := {} }
  e.submit (Task.Item.ofAction (a.step (fun v => done.set (some v)) ctx))
  blockOnWith e now idle (do return (← done.get).isSome)
  match ← done.get with
  | some v => return v
  | none   => throw (IO.userError "Runtime.run: the driver stopped before the computation finished")

/-- Run one computation to completion on the caller's thread and return its value: `runWith` with the live clock
reader and no idle step. -/
def run (e : Executor cap) (a : Task.Async α) : IO α :=
  runWith e IO.monoNanosNow (do return false) a

end LeanIn.Runtime
