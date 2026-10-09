import Std
import LeanIn.Runtime.Leaf
import LeanIn.Task.Error

/-!
# The blocking pool

`docs/tokio-workplan.md` W4: a bounded pool of carrier threads off the executor's queue, with its own queue
and its own shutdown, for the leaves that genuinely block — the synchronous `IO` APIs, foreign calls and
CPU-bound work. Not DNS (`uv_getaddrinfo` already runs on libuv's own pool) and not file wrappers: the pool
is a *route* blocking work takes, and it stays bounded and separable.

**What exists here.** The pool: `BlockingPool.new` starts a fixed number of workers, each an
`IO.asTask … Task.Priority.dedicated` running `BlockingPool.workerLoop` over the pool's own queue, parked on
the pool's own condvar, with `submit`, `shutdown` and `shutdownAndWait` as the operations over it. The
submission path is on it: `spawnBlocking` derives from `spawnBlockingE`, whose step registers the job's
liveness witness in `Hooks` (so `Runtime.pending` counts a blocking job exactly as it counts a leaf
registration) and submits the job to the pool; when the job finishes on a pool thread it resolves that
witness and delivers the completion through `ctx.resume`. The handle is the ordinary `Task.Task α` the task
layer already produces for a spawned computation, so `await`, `Runtime.cancel` and `concurrently` work on a
blocking job with no new handle type and no new instance.

**The completion goes through `ctx.resume`, not `k`.** `k` is the continuation of the *submitting* step; if
the job thread ran it, the computation would continue on the job thread and everything downstream of it would
too. `ctx.resume` is the runtime's scheduling function, so the completion is delivered as a fresh item on the
carrier, and it stamps that item with `ctx.cancel` — so if the submitting computation is cancelled, `Item.fire`
skips the completion even though the job itself cannot be stopped: a cancelled computation runs no further
step of it. A failing job catches its own failure, so it cannot kill a pool worker and leave the exited count
short of `shutdownAndWait`'s wait.

**The park/wake protocol is the executor's.** A `List (IO Unit)` under the pool's own `Std.Mutex`, a worker
take through `Mutex.atomicallyOnce`, and a submitter that appends and notifies **unconditionally under the
same lock** (`LeanIn/Sched/Executor.lean`): the predicate is re-checked under the lock the notification is
made under, so a wakeup cannot be lost in the gap between deciding to park and parking. There is
deliberately no `parked` counter — a notification does not depend on one being recorded.

**The pool is not part of the executor, the model, `Item` or `Hooks`.** Its threads hold no executor state
and take no items, so the single-carrier statement (`State.Aligned`) is unchanged; the pool's own counts
live on the pool under the pool's lock, not in `Executor.State`.

**Lifetime is the caller's.** `new` has no default width and there is no global pool: the width is the
caller's argument and the caller shuts the pool down. A width of zero is the one rejected: a pool with no
worker would accept a job no thread can run, and `shutdownAndWait`'s predicate `exited == workers` would be
`0 == 0` at once, so `new` throws and names the width rather than hand back a pool that can serve nothing.
`shutdownAndWait` drains the queue and then waits for every worker to exit; a job that never returns makes
that wait unbounded, which is stated here rather than promised away.
-/

namespace LeanIn.Runtime

/-- The pool's own state, under the pool's own lock: the FIFO job queue (oldest at the head), the shutdown
flag, and how many workers have exited. -/
structure PoolState where
  queue    : List (IO Unit)
  stopping : Bool
  exited   : Nat

/-- **A bounded pool of blocking workers.** One lock over the queue and the shutdown bookkeeping, one
condvar the workers park on, and the width the caller chose. -/
structure BlockingPool where
  state   : Std.Mutex PoolState
  cv      : Std.Condvar
  workers : Nat

namespace BlockingPool

/-- **Take one job, or report the pool drained and stopped.** The predicate is re-checked under the lock the
notification is made under, so a worker that finds nothing parks *inside* this critical section and a
submitter cannot slip between the check and the park. `none` means the queue is empty *and* the pool is
stopping — a stopping pool still serves what it holds, so this is a drain rather than an abrupt exit. -/
def take (p : BlockingPool) : IO (Option (IO Unit)) :=
  p.state.atomicallyOnce p.cv
    (pred := do
      let st ← get
      return !st.queue.isEmpty || st.stopping)
    (k := do
      let st ← get
      match st.queue with
      | []        => return none
      | j :: rest => set { st with queue := rest }; return (some j))

/-- **Record that a worker has exited**, and wake whoever is waiting on the count. -/
def finish (p : BlockingPool) : IO Unit :=
  p.state.atomically do
    let st ← get
    set { st with exited := st.exited + 1 }
    p.cv.notifyAll

/-- **One worker's loop.** Take a job and run it, until the pool is stopping and drained, then record the
exit. A job is expected not to throw: a worker that died under one would leave the exited count short and
hang `shutdownAndWait`, so a job that can fail catches its own failure. -/
def workerLoop (p : BlockingPool) : IO Unit := do
  let mut go := true
  while go do
    match ← take p with
    | some job => let _ ← job; pure ()
    | none     => go := false
  finish p

/-- **Start a pool of `workers` blocking workers.** A width of zero is rejected before anything is started: a
pool with no worker would accept a job no thread can run and `shutdownAndWait` at once, so a silent pool that
serves nothing is the near-silent failure a loud throw replaces. One `IO.asTask … Task.Priority.dedicated` per
remaining worker — a dedicated OS thread each, `Task.Priority.dedicated` being above `Task.Priority.max`. The
handles are dropped: an `IO.asTask` task runs even with no reference to it, and the loop's own stop flag is what
ends a worker's shift. -/
def new (workers : Nat) : IO BlockingPool := do
  if workers == 0 then
    throw (IO.userError s!"BlockingPool.new: width {workers} starts no workers, so a submitted job could \
      never run and shutdownAndWait would return at once; the width must be at least one")
  let p : BlockingPool :=
    { state := ← Std.Mutex.new { queue := [], stopping := false, exited := 0 },
      cv := ← Std.Condvar.new,
      workers := workers }
  for _ in List.range workers do
    let _ ← IO.asTask (workerLoop p) _root_.Task.Priority.dedicated
    pure ()
  return p

/-- **Submit one job.** Append and notify, in one critical section; a submit to a stopping pool throws,
because a job no worker will take would hang whoever awaits it. The notify is unconditional: there is no
parked counter to consult, and a notification with no waiter is lost but harmless, since a worker that
parks afterwards re-checks the predicate under this same lock. -/
def submit (p : BlockingPool) (j : IO Unit) : IO Unit :=
  p.state.atomically do
    let st ← get
    if st.stopping then
      throw (IO.userError "BlockingPool.submit: the pool is shutting down")
    else
      set { st with queue := st.queue ++ [j] }
      p.cv.notifyOne

/-- **Shut the pool down.** Set the stop flag and wake every worker; the workers drain what is queued before
they see the flag, so a job submitted before the shutdown still runs. -/
def shutdown (p : BlockingPool) : IO Unit :=
  p.state.atomically do
    let st ← get
    set { st with stopping := true }
    p.cv.notifyAll

/-- **Shut down and wait for every worker to exit.** A worker exits only when the pool is stopping and the
queue is empty, so this waits for the queue to drain as well. A job that never returns makes the wait
unbounded. -/
def shutdownAndWait (p : BlockingPool) : IO Unit := do
  shutdown p
  p.state.atomicallyOnce p.cv
    (pred := do return (← get).exited == p.workers)
    (k := pure ())

end BlockingPool

/-- **Run a blocking action whose failure is a value** — the sibling of `spawnBlocking`, in the shape the
leaf seam's panicking/`…E` pair has, for a caller that treats a failed job as an ordinary event.

The step registers the job's liveness witness in `Hooks` — one promise, and the derived task `Runtime.pending`
reads, neither of which costs a thread — and then submits the job to the pool. When the job finishes on a pool
thread it resolves that witness and delivers the completion through `ctx.resume`, so the awaiting computation
continues on the carrier and not on the job's thread; the failure rides in the value, as `EAsync` does
everywhere else. The job catches its own failure here, so a failing job cannot kill a pool worker. -/
def spawnBlockingE (p : BlockingPool) (hooks : Hooks) (act : IO α) : Task.EAsync IO.Error α :=
  ⟨fun k ctx => do
     -- The liveness witness `pending` reads. One promise and one derived task per job; both are the
     -- stock machinery the leaf seam already reaches, and neither costs a thread.
     let done ← IO.Promise.new (α := Unit)
     hooks.add ctx.cancel ((done.result?).map (fun _ => ()) (sync := true))
     -- `submit` throws only when the pool is stopping, so the job below never runs and nothing else
     -- would ever resolve `done`. Resolve it here, before the throw propagates, rather than reorder the
     -- registration after the submission: `pending` counts the witness until its stock `Task` finishes,
     -- so a failed submission that skipped this would leave a counted entry for a job that can never
     -- finish. Resolving on the failure path keeps the registration before the submission, as the step's
     -- description above states, and settles precisely the one entry this submission registered.
     try
       p.submit (do
          let r : Except IO.Error α ← try Except.ok <$> act catch e => pure (.error e)
          done.resolve ()
          ctx.resume (Task.Item.ofAction (k r)))
     catch e => done.resolve (); throw e⟩

/-- **Run a blocking action**, carrying no failure channel: the failure is a defect, so a failing job is a
panic rather than a value. It derives from `spawnBlockingE` — the job is submitted to the pool and its
completion resumes the awaiting computation on the carrier. The handle is the ordinary `Task.Task α` the task
layer gives a spawned computation, so `await`, `Runtime.cancel` and `concurrently` work on it unchanged and no
new handle type is introduced. -/
def spawnBlocking (p : BlockingPool) (hooks : Hooks) (act : IO α) : Task.Async α :=
  ⟨fun k ctx => (spawnBlockingE p hooks act).step
     (fun r => match r with
       | .ok v    => k v
       | .error e => panic! s!"spawnBlocking: the blocking job failed: {e}") ctx⟩

end LeanIn.Runtime
