import Std

/-!
# The single-carrier scheduler

M3's spine: a ready queue, a carrier loop over it, and `blockOn`, which drives the queue on the
*caller's* thread. The park protocol is the one the model's A5 forces and the M0 waker spike
demonstrated — push and notify **under the same lock**, take by parking on a predicate re-checked
under that lock — so a notification cannot be lost in the gap between deciding to park and parking.

A job is polled: it does its work and returns whether it has finished. One that has not finished is
expected to have re-enqueued itself, or arranged for whoever completes it to enqueue it; that is the
whole of the protocol, and it is why `Job` is a *value* and can simply be pushed again.

Not here yet, and named rather than implied: the `Task`/`Async` layer with `MonadAsync`/`MonadAwait`
(`LeanIn/Task/`), the inject queue as a distinct structure (M5), and the blocking pool (M4). This is the
structure the milestone's refinement obligations are about, and the model's `Pool`/`Scheduler` are what
it must be matched against — `Impl.push ⊑ Model.push` and the rest of `interface.md` §6.
-/

namespace LeanIn.Sched

/-- A polled job: `true` when it has finished. A job that parks returns `false` and is enqueued again
when whatever it is waiting for completes. -/
abbrev Job := IO Bool

/-- **The inject queue**: the model's `inject`, "the shared queue receiving overflow. Unbounded." One
mutex, one condvar, a stop flag, and a list — because that is what the model says it is, and because it is
pushed from any thread, the waker included.

It is *not* the model's `ring` and not its `lifo` slot, and the difference is not cosmetic. `ring` is
bounded — `Pool.Bounded p` is `p.ring.length ≤ p.cap`, 256 in Tokio — and owner-local, submitted at the back
and taken from the front, while `lifo` is a single owner-local slot that is never stolen. This queue is
neither, and giving it a capacity would be a claim nothing here checks. When the executor grows the ring it
belongs in `LeanIn/Data/Ring.lean` — M2b, already verified — and `tests/executor-contract.sh SC5` is the
contract that will demand it: its receipts are the batch that crossed the ring's capacity, the takes from
the LIFO slot, and the flush of a pending continuation. -/
structure Queue where
  lock     : Std.Mutex (List Job)
  cv       : Std.Condvar
  stopping : IO.Ref Bool

namespace Queue

def new : IO Queue := do
  return { lock := ← Std.Mutex.new ([] : List Job),
           cv := ← Std.Condvar.new,
           stopping := ← IO.mkRef false }

/-- Push and notify **under the same lock**. The model proves the notification can be lost
(`notifyOne_no_waiters`); the discipline here is what stops it being lost *while a carrier is parking*,
which is the case no model theorem can rule out for us. -/
def push (q : Queue) (j : Job) : IO Unit :=
  q.lock.atomically do
    set ((← get) ++ [j])
    q.cv.notifyOne

/-- Take, parking until a job arrives or the queue is stopping. -/
def take (q : Queue) : IO (Option Job) :=
  q.lock.atomicallyOnce q.cv
    (pred := do return !(← get).isEmpty || (← q.stopping.get))
    (k := do
      let js ← get
      match js with
      | []       => return none
      | j :: js' => set js'; return (some j))

/-- Stop: further takes return nothing once the queue drains. -/
def stop (q : Queue) : IO Unit := do
  q.stopping.set true
  q.lock.atomically do q.cv.notifyAll

end Queue

/-- The carrier loop: poll jobs until the queue is stopped. -/
def carrier (q : Queue) : IO Unit := do
  let mut go := true
  while go do
    match ← Queue.take q with
    | some j => let _ ← j; pure ()
    | none   => go := false

/-- **Drive the queue on this thread until `finished` reports true.** "Drive the executor on the
caller's thread": the single-carrier executor has no other thread to hand the wait to, so the caller
polls the queue itself and parks in `take` when nothing is ready. -/
def blockOn (q : Queue) (finished : IO Bool) : IO Unit := do
  let mut go := true
  while go do
    if ← finished then go := false
    else
      match ← Queue.take q with
      | some j => let _ ← j; pure ()
      | none   => go := false

end LeanIn.Sched
