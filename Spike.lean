import Std

/-!
Measurement harness for the `leanin` plan. Not part of the library.

Run with `lake exe spike`. Every number printed here is evidence about the
scheduler Lean 4.35 ships; the plan's milestone ordering is calibrated against it.
-/

namespace Spike

open Std
open Std.Async

/-- Distinct OS thread ids observed across `n` tasks spawned at priority `prio`. -/
def tidsOf (n : Nat) (prio : Task.Priority) : IO (Array UInt64) := do
  let tasks ← (List.range n).mapM (fun _ => IO.asTask (IO.getTID) prio)
  let res ← tasks.mapM (fun t => IO.wait t)
  let mut acc : Array UInt64 := #[]
  for r in res do
    match r with
    | .ok tid => if !acc.contains tid then acc := acc.push tid
    | .error _ => pure ()
  return acc

/-- Run `x`, returning its result and the elapsed wall-clock milliseconds. -/
def timed (x : IO α) : IO (α × Nat) := do
  let t0 ← IO.monoMsNow
  let a ← x
  let t1 ← IO.monoMsNow
  return (a, t1 - t0)

/-- Wall-clock ms for `n` concurrent `IO.sleep d` tasks, and for `n` serial ones. -/
def sleepProbe (n : Nat) (d : UInt32) (prio : Task.Priority) : IO (Nat × Nat) := do
  let (_, par) ← timed do
    let ts ← (List.range n).mapM (fun _ => IO.asTask (IO.sleep d) prio)
    let _ ← ts.mapM (fun t => IO.wait t)
    pure ()
  let (_, ser) ← timed do
    for _ in List.range n do IO.sleep d
  return (par, ser)

/-- Elapsed ms for two `IO.sleep d` computations raced under `Async.async`/`await`. -/
def asyncProbe (d : UInt32) : IO Nat := do
  let (_, t) ← timed do
    Std.Async.Async.block do
      let a ← async (IO.sleep d)
      let b ← async (IO.sleep d)
      let _ ← await a
      let _ ← await b
      pure ()
  return t

/-- Elapsed ms for `n` concurrent `Async.sleep` (libuv timer) computations. -/
def asyncSleepProbe (n : Nat) (d : Std.Time.Millisecond.Offset) : IO Nat := do
  let (_, t) ← timed do
    Std.Async.Async.block do
      let ts ← (List.range n).mapM (fun _ => async (Std.Async.sleep d))
      discard <| ts.forM (fun t => await t)
      pure ()
  return t

/-- A `Promise` resolved from the main task, awaited on a spawned task. -/
def promiseProbe : IO Nat := do
  let p ← IO.Promise.new (α := Nat)
  let c ← IO.asTask (do
    let r ← IO.wait p.result?
    return r.getD 0) Task.Priority.default
  IO.sleep 50
  p.resolve 42
  match ← IO.wait c with
  | .ok v => return v
  | .error e => throw e

/-- Sum `0..n-1` through a bounded `CloseableChannel`, one producer task. -/
def channelProbe (n : Nat) (cap : Option Nat) : IO (Except CloseableChannel.Error Nat) := do
  let ch ← CloseableChannel.new (α := Nat) (capacity := cap)
  let producer ← IO.asTask (do
    for i in List.range n do
      let t ← ch.send i
      let _ ← IO.wait t
    let _ ← ch.close.toBaseIO
    pure ()) Task.Priority.default
  let mut sum := 0
  let mut done := false
  while !done do
    let t ← ch.recv
    match ← IO.wait t with
    | some v => sum := sum + v
    | none => done := true
  let _ ← IO.wait producer
  return .ok sum

end Spike

open Spike

/-- Root entry point; must be at root scope or the toolchain links the default `_lean_main`. -/
def main : IO UInt32 := do
  let cores := System.Platform.Internal.getHardwareConcurrency ()
  IO.println s!"hardware concurrency: {cores}"
  let d ← tidsOf 64 Task.Priority.default
  IO.println s!"64 tasks, default prio   : {d.size} distinct threads"
  let d9 ← tidsOf 64 Task.Priority.dedicated
  IO.println s!"64 tasks, dedicated prio : {d9.size} distinct threads"
  let (par, ser) ← sleepProbe 64 100 Task.Priority.default
  IO.println s!"64x IO.sleep 100ms, default   : parallel {par}ms / serial {ser}ms"
  let (par9, _) ← sleepProbe 64 100 Task.Priority.dedicated
  IO.println s!"64x IO.sleep 100ms, dedicated : parallel {par9}ms"
  let elapsed ← asyncProbe 200
  IO.println s!"Async.async 2x IO.sleep 200ms: {elapsed}ms"
  IO.println s!"64x Async.sleep 100ms        : {← asyncSleepProbe 64 100}ms"
  IO.println s!"Promise handoff: {← promiseProbe}"
  IO.println s!"Channel sum 0..99 (bounded 4): {← channelProbe 100 (some 4)}"
  IO.println s!"Channel sum 0..99 (unbounded): {← channelProbe 100 none}"
  return 0
