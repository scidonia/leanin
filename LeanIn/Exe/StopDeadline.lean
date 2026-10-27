module

import LeanIn

/-!
`lake exe stopDeadline` parks a scoped `VM.sleep` for 60 s, calls `stopWithDeadline` with a 100 ms
grace, and checks that the scope ends `aborted` within a bounded time rather than waiting for the sleep.
-/

open LeanIn

public def main : IO UInt32 := do
  let hooks ← Runtime.Hooks.new
  let clock := Runtime.Clock.live hooks
  let e ← Sched.Executor.new LeanIn.Task.Item 256 1
  let out ← IO.mkRef (none : Option (Runtime.Outcome Unit))
  let prog : LeanIn.Task.EAsync IO.Error Unit :=
    ⟨fun k ctx => Runtime.VM.runAsync (Runtime.VM.requestScope (Runtime.VM.sleep clock 60000))
      (fun o => do out.set (some o); k (.ok ()) ctx)⟩
  let t ← IO.asTask (Runtime.run e prog) _root_.Task.Priority.dedicated
  IO.sleep 50
  let t0 ← IO.monoNanosNow
  Runtime.stopWithDeadline e 100
  let _ ← IO.wait t
  let elapsedMs := ((← IO.monoNanosNow) - t0) / 1000000
  match ← out.get with
  | some (.aborted _) =>
    IO.println s!"stopDeadline|aborted=yes|elapsedMs={elapsedMs}"
    if elapsedMs < 2000 then return 0 else return 1
  | some (.ok _) => IO.eprintln "stopDeadline: scope completed normally"; return 1
  | some (.error e) => IO.eprintln s!"stopDeadline: scope errored: {e}"; return 1
  | none => IO.eprintln "stopDeadline: scope never resolved"; return 1
