import Std
import Std.Async.Timer
import LeanIn.Runtime.Leaf
import LeanIn.Task.Basic

/-!
# Time on our carriers

W3: the timer leaf, and the one combinator a service cannot do without — `withTimeout`. The timers stay
`Std.Async`'s, on libuv's loop, and are awaited through W1's seam exactly as the sockets are; what is ours is
the combination, because a timeout is a *race* between a computation and a clock.

**Why a race needs its own resolution.** The task layer's `Join.resolve` states that a handle has one writer and
is loud when that is broken, which is right for a normal completion and wrong for a race: there, two writers are
the design and one of them must lose. `Join.resolveFirst` is that second law, and it is the whole of what this
file adds to the task layer.

**The timer is not cancelled when the computation wins.** A `withTimeout` that returns because its computation
finished leaves the timer pending until it fires, which costs one parked task and nothing else. Cancelling it
needs a handle on the timer — the promise and `Task` seam is where one would come from, and it is W7's item — and
the operation that drops scheduled work, which is `Runtime.cancel` (W5). So this is a combinator that is correct
about its *result* and honest about what it leaves behind: what it leaves is a timer that will fire with nobody
waiting, rather than a cancellation.
-/

namespace LeanIn.Runtime

/-- **Sleep, awaited as one of ours.** The wait costs no carrier: the timer belongs to libuv's loop and its
completion enqueues our resume, so a carrier that is sleeping is a carrier that is parked. -/
def sleep (hooks : Hooks) (d : Std.Time.Millisecond.Offset) : Task.Async Unit :=
  awaitAsync hooks (Std.Async.sleep d)

/-- **A computation that never finishes.** A step that registers no continuation and calls none is exactly
that: nothing will ever schedule it again. It is what a timeout needs in order to actually time out, and it
needs no clock to say so. -/
def never {α : Type} : Task.Async α :=
  ⟨fun _ _ => pure ()⟩

/-- **`a`, or `none` if `d` elapses first.** The first writer wins — the computation's own value, or the
timer's `none` — and the loser's write is ignored rather than being a defect. -/
def withTimeout (hooks : Hooks) (d : Std.Time.Millisecond.Offset) (a : Task.Async α) :
    Task.Async (Option α) := do
  let cell ← Task.Join.new
  Task.background (do
    let v ← a
    Task.Join.resolveFirst cell (some v))
  Task.background (do
    sleep hooks d
    Task.Join.resolveFirst cell none)
  let token ← (Task.Cancel.new : IO Task.Cancel)
  Task.Async.await (show Task.Task (Option α) from ⟨cell, token⟩)

end LeanIn.Runtime
