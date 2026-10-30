module

import LeanIn

/-! `lake exe queueScaling`: does a queue's per-operation cost stay put as the queue gets deeper?

A functional proof cannot see this. `Deque`'s laws held while every operation copied the whole store, because
sharing is a property of the runtime's reference counts and not of the values. So the check is empirical, and it
keeps an empirical check's limits: it compares two timings taken in one process, and can falsify "per-operation
cost is independent of depth" without establishing it.

Each case is timed at a shallow and a deep depth on one thread, with no contention, on a cell another thread has
already seen, because that is the state a running executor's cells are in. The detector is `ratio`: deep ns/op
over shallow ns/op, best of `rounds` at each depth so a loaded host can only hide a rise, not invent one.

The affirmative control runs the same detector over an `Array` written through the placeholder idiom on a shared
cell, which copies on every write, so a detector that went blind is a setup failure rather than a pass. -/

open LeanIn LeanIn.Runtime

abbrev It := LeanIn.Task.Item

def item : It := LeanIn.Task.Item.ofAction (pure ())

def shallow : Nat := 1000
def deep : Nat := 16000
def rounds : Nat := 3
/-- A linear queue reads about `deep / shallow` here, and a flat one under 2. -/
def limit : Float := 5.0

/-- Make `touch`'s cell multi-threaded the way a carrier does: another thread reaches it. -/
def share (touch : IO Unit) : IO Unit := do
  let t ← IO.asTask touch _root_.Task.Priority.dedicated
  let _ ← IO.wait t

/-- The control: what the inject's store was. Every write is a copy once the cell has been shared. -/
def arrayCell (depth : Nat) : IO Nat := do
  let cell ← Std.Mutex.new (Array.replicate depth (none : Option It))
  share (cell.atomically (pure ()))
  let t0 ← IO.monoNanosNow
  for i in [0:depth] do
    cell.atomically do
      let a ← get
      set (#[] : Array (Option It))
      set (a.setIfInBounds i (some item))
  for i in [0:depth] do
    cell.atomically do
      let a ← get
      set (#[] : Array (Option It))
      set (a.setIfInBounds i none)
  return (← IO.monoNanosNow) - t0

/-- The shared inject: fill it, then drain it, which is the backlog a spawn burst leaves. -/
def inject (depth : Nat) : IO Nat := do
  let e ← Sched.Executor.new It 256 1
  share (do let _ ← e.isStopping)
  let t0 ← IO.monoNanosNow
  for _ in [0:depth] do e.pushInjectRaw item
  for _ in [0:depth] do let _ ← e.popInject
  return (← IO.monoNanosNow) - t0

/-- The timer hand-off: arm `depth` timers from one step, so the driver cannot drain them in between. The closing
sleep lets it drain them outside the timed section, so one round's backlog is not the next one's starting depth. -/
def timers (depth : Nat) : IO Nat := do
  let e ← Sched.Executor.new It 256 1
  let c := Clock.live (← Hooks.new)
  Runtime.run e do
    let t0 ← (IO.monoNanosNow : IO Nat)
    for _ in [0:depth] do
      let cancel ← (LeanIn.Task.Cancel.new : IO LeanIn.Task.Cancel)
      c.schedule 3600000 cancel (pure ())
    let t1 ← (IO.monoNanosNow : IO Nat)
    sleep c 1
    return t1 - t0

/-- The best of `rounds` timings, as ns per operation. -/
def nsPerOp (measure : Nat → IO Nat) (depth : Nat) : IO Float := do
  let mut ns : Nat := 0
  for i in [0:rounds] do
    let t ← measure depth
    ns := if i == 0 then t else min ns t
  return ns.toFloat / depth.toFloat

/-- **The detector.** One record, and whether the rise is over the limit. -/
def ratio (name : String) (measure : Nat → IO Nat) : IO Bool := do
  let a ← nsPerOp measure shallow
  let b ← nsPerOp measure deep
  let r := b / a
  let over := decide (r ≥ limit)
  IO.println s!"queueScaling|case={name}|shallow={shallow}|deep={deep}|nsShallow={a}|nsDeep={b}|ratio={r}|limit={limit}|rises={over}"
  (← IO.getStdout).flush
  return over

public def main : IO UInt32 := do
  unless ← ratio "control-array" arrayCell do
    IO.println "queueScaling|setup=detector did not flag the copying control"
    IO.Process.exit 2
  let injectRises ← ratio "inject" inject
  let timersRise ← ratio "timers" timers
  -- `Process.exit` rather than a return: the timers still on the wheel would hold the process open for their hour.
  IO.Process.exit (if injectRises || timersRise then 1 else 0)
