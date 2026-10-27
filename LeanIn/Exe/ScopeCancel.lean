module

import LeanIn

/-!
`lake exe scopeCancel` runs a request scope parked in a 60 s sleep, cancels the scope, and checks that the
request ends `aborted`, the timer is retired immediately, and the scope's cleanup runs exactly once.
-/

open LeanIn

public def main : IO UInt32 := do
  let hooks ← Runtime.Hooks.new
  let clock := Runtime.Clock.live hooks
  let e ← Sched.Executor.new LeanIn.Task.Item 256 1
  let scope ← Runtime.Scope.new
  let exits ← IO.mkRef (0 : Nat)
  Runtime.Scope.onExit scope (exits.modify (· + 1))
  let out ← IO.mkRef (none : Option (Runtime.Outcome Unit))
  let prog : LeanIn.Task.EAsync IO.Error Unit :=
    ⟨fun k ctx =>
      Runtime.VM.runAsyncScoped scope
        (Runtime.VM.requestScope (Runtime.VM.sleep clock 60000))
        (fun o => do out.set (some o); k (.ok ()) ctx)⟩
  let t ← IO.asTask (Runtime.run e prog) _root_.Task.Priority.dedicated
  IO.sleep 50
  let t0 ← IO.monoNanosNow
  Runtime.Scope.cancelNow scope
  let _ ← IO.wait t
  let elapsedMs := ((← IO.monoNanosNow) - t0) / 1000000
  let firstExits ← exits.get
  Runtime.Scope.cancelNow scope
  Runtime.Scope.exit scope
  let secondExits ← exits.get
  let aborted := match ← out.get with | some (.aborted _) => true | _ => false
  -- A child scope is cancelled with its parent, and its own cleanup runs once.
  let hooks2 ← Runtime.Hooks.new
  let clock2 := Runtime.Clock.live hooks2
  let e2 ← Sched.Executor.new LeanIn.Task.Item 256 1
  let parent ← Runtime.Scope.new
  let child ← Runtime.Scope.child parent
  let childExits ← IO.mkRef (0 : Nat)
  Runtime.Scope.onExit child (childExits.modify (· + 1))
  let childOut ← IO.mkRef (none : Option (Runtime.Outcome Unit))
  let childProg : LeanIn.Task.EAsync IO.Error Unit :=
    ⟨fun k ctx =>
      Runtime.VM.runAsyncScoped child
        (Runtime.VM.requestScope (Runtime.VM.sleep clock2 60000))
        (fun o => do childOut.set (some o); k (.ok ()) ctx)⟩
  let ct ← IO.asTask (Runtime.run e2 childProg) _root_.Task.Priority.dedicated
  IO.sleep 50
  Runtime.Scope.cancelNow parent
  let _ ← IO.wait ct
  let childAborted := match ← childOut.get with | some (.aborted _) => true | _ => false
  let childExitCount ← childExits.get
  IO.println s!"scopeCancel|aborted={aborted}|elapsedMs={elapsedMs}|exits={firstExits}|exitsAfterRepeat={secondExits}|childAborted={childAborted}|childExits={childExitCount}"
  if aborted && elapsedMs < 200 && firstExits == 1 && secondExits == 1 &&
      childAborted && childExitCount == 1 then return 0 else return 1
