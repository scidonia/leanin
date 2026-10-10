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

/-- **Spawn from outside a body**: the ring, because there is no current worker's slot to use — the interface's
"or inject if called from outside". -/
def spawn (e : Executor cap) (a : Task.Async α) : IO (Task.Task α) := do
  let cell ← Task.Join.new
  let cancel ← Task.Cancel.new
  let ctx : Task.Ctx := { cancel := cancel, resume := fun it => resumeOf e (it.stamp cancel), «local» := {} }
  e.submit (Task.Item.stamp (Task.Item.ofAction (a.step (fun v => Task.Join.resolve cell v) ctx)) cancel)
  return ⟨cell, cancel⟩

/-- **Drive the executor on the caller's thread** until `finished` holds.

This is the single-carrier claim as code: there is no other thread to hand the wait to, so the caller runs the
item itself and parks in `work` when nothing is ready. That park is the protocol's — the predicate is re-checked
under the same lock a submit notifies under — so a completion arriving while this thread is parked wakes it
rather than being lost. -/
def blockOn (e : Executor cap) (finished : IO Bool) : IO Unit := do
  let mut go := true
  while go do
    if ← finished then go := false
    else
      match ← e.work with
      | some it => it.fire
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

/-- Run one computation to completion on the caller's thread and return its value.

The completion is a cell the computation's own last step writes, so the driver's stop condition is the value
arriving rather than a clock or a count. If the driver stops for another reason — the pool stopping — the
missing value is reported rather than filled in with a default. -/
def run (e : Executor cap) (a : Task.Async α) : IO α := do
  let done ← IO.mkRef (none : Option α)
  -- The driver's own computation carries a token nothing hands out, and its first item is left unstamped: `run`
  -- is a caller's thread waiting, and the computation it drives is not one another task holds a handle to.
  let ctx : Task.Ctx := { cancel := ← Task.Cancel.new, resume := resumeOf e, «local» := {} }
  e.submit (Task.Item.ofAction (a.step (fun v => done.set (some v)) ctx))
  blockOn e (do return (← done.get).isSome)
  match ← done.get with
  | some v => return v
  | none   => throw (IO.userError "Runtime.run: the driver stopped before the computation finished")

end LeanIn.Runtime
