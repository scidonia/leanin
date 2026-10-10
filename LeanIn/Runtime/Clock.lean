import Std
import Std.Async.Timer
import LeanIn.Runtime.Basic
import LeanIn.Runtime.Leaf

/-!
# The clock seam

The runtime's time enters as a parameter. `Clock` is a record of the two operations a computation needs from a
clock — a monotone reading in nanoseconds, and a one-shot wait — and `Runtime.sleep`/`Runtime.withTimeout` take
one. `Clock.live` is today's composition: `IO.monoNanosNow` for the reading, and the libuv timer behind W1's
seam for the wait, so the production path is the same code it always was, reached through a record instead of
directly.

The second implementation is the point of the seam. `HarnessClock` keeps a virtual instant and a sorted list of
pending timers under one mutex, and `HarnessClock.advance` moves the instant to the earliest deadline and fires
that timer. A driver that installs it decides one instant at a time: nothing is registered with libuv, so no
live clock is read anywhere on a harness run, and an instant is read as a number rather than waited out.

`runVirtual` is that driver: `Runtime.runWith`, the general entry, with this clock's reading and
`HarnessClock.advance` as the idle step. When nothing can be advanced to it parks exactly as the live driver
does, which is what keeps it composable with a leaf or with another thread's delivery — and means a mode that
awaits a gate nobody resolves hangs and is bounded by a watchdog rather than mis-reported as a wrong reading.

No production primitive is added here: `Clock.live` composes two things already on the register, and
`HarnessClock` calls no clock at all — its whole mechanism is one mutex over pure list and natural-number code.
-/

namespace LeanIn.Runtime

/-- **What a computation asks of a clock.** `now` is monotone nanoseconds; `sleep d` is a one-shot wait on
whichever clock is installed, awaited as one of ours so the waiter parks rather than occupies a carrier. -/
structure Clock where
  /-- The current instant, in monotone nanoseconds. -/
  now   : IO Nat
  /-- A one-shot wait for `d` from now. -/
  sleep : Std.Time.Millisecond.Offset → Task.Async Unit

/-- **The production clock**: the live reading and the libuv timer behind W1's seam. -/
def Clock.live (hooks : Hooks) : Clock :=
  { now   := IO.monoNanosNow
  , sleep := fun d => awaitAsync hooks (Std.Async.sleep d) }

/-- The virtual clock's state: the current instant and its pending timers, sorted by instant and FIFO on
ties. -/
structure HarnessState where
  /-- Virtual nanoseconds. -/
  now    : Nat := 0
  /-- The pending timers, earliest first. -/
  timers : List (Nat × IO Unit) := []
deriving Inhabited

/-- **A clock the harness drives.** Nothing registered with libuv: an instant is a number and a fire is a list
element. -/
structure HarnessClock where
  state : Std.Mutex HarnessState

/-- A harness clock at virtual instant zero with nothing pending. -/
def HarnessClock.new : IO HarnessClock :=
  return ⟨← Std.Mutex.new ({} : HarnessState)⟩

/-- The current virtual instant — the reading a scenario compares its stated instants against. -/
def HarnessClock.now (hc : HarnessClock) : IO Nat :=
  hc.state.atomically do return (← get).now

/-- How many timers are pending. -/
def HarnessClock.pending (hc : HarnessClock) : IO Nat :=
  hc.state.atomically do return (← get).timers.length

/-- **Schedule a fire at `instant`**, keeping the list sorted and FIFO among equal instants. -/
def HarnessClock.schedule (hc : HarnessClock) (instant : Nat) (fire : IO Unit) : BaseIO Unit :=
  hc.state.atomically do
    let s ← get
    let rec ins : List (Nat × IO Unit) → List (Nat × IO Unit)
      | []              => [(instant, fire)]
      | (t, f) :: rest  => if instant < t then (instant, fire) :: (t, f) :: rest else (t, f) :: ins rest
    set { s with timers := ins s.timers }

/-- **Advance to the earliest pending timer**: set the virtual instant to its `instant` and run its fire, outside
the lock. `false` when nothing is pending — the driver then parks as the live one does. -/
def HarnessClock.advance (hc : HarnessClock) : IO Bool := do
  let due ← hc.state.atomically do
    let s ← get
    match s.timers with
    | []                  => return none
    | (instant, fire) :: rest  => set { s with now := instant, timers := rest }; return (some fire)
  match due with
  | none      => return false
  | some fire => fire; return true

/-- **The clock this harness drives.** Its `sleep` schedules a fire and returns: the wait is a list insertion,
and the fire runs when the driver advances to it, resuming the awaiter on the driver's own thread. -/
def HarnessClock.clock (hc : HarnessClock) : Clock :=
  { now   := hc.now
  , sleep := fun d => ⟨fun k ctx => do
      let fire : IO Unit := do ctx.resume (Task.Item.ofAction (k ()))
      let now0 ← hc.now
      hc.schedule (now0 + d.val.toNat) fire
      return ()⟩ }

/-- **Run a computation with a harness clock driving it.** The general driver with this clock's reading for the
metered path and one advance per idle round for the pool-empty wait. -/
def runVirtual (hc : HarnessClock) (e : Executor cap) (a : Task.Async α) : IO α :=
  runWith e hc.now hc.advance a

end LeanIn.Runtime
