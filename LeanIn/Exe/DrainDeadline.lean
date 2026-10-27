module

import LeanIn

/-!
`lake exe drainDeadline` starts an accept loop with a 100 ms drain deadline, connects a client, and parks the
handler in a scoped 60 s sleep. Stopping the executor must abort that request at the deadline, run its cleanup
exactly once, and return the loop within a bounded time.
-/

open LeanIn

public def main : IO UInt32 := do
  let hooks ← Runtime.Hooks.new
  let clock := Runtime.Clock.live hooks
  let e ← Sched.Executor.new LeanIn.Task.Item 256 1
  let l ← Runtime.Listener.bind (Runtime.loopback 0)
  let started ← (IO.Promise.new : IO (IO.Promise (Except IO.Error Unit)))
  let outcome ← IO.mkRef (none : Option (Runtime.Outcome Unit))
  let exits ← IO.mkRef (0 : Nat)
  let body (_ : Runtime.Conn) : LeanIn.Task.EAsync IO.Error Unit :=
    ⟨fun k ctx => do
      let scope ← Runtime.Scope.new
      Runtime.Scope.onExit scope (exits.modify (· + 1))
      IO.Promise.resolve (Except.ok ()) started
      Runtime.VM.runAsyncScoped scope
        (Runtime.VM.requestScope (Runtime.VM.sleep clock 60000))
        (fun o => do outcome.set (some o); k (.ok ()) ctx)⟩
  let serverProg : LeanIn.Task.EAsync IO.Error Unit :=
    Runtime.serveUntilStoppedWithDeadline hooks e l 1 100 body []
  let serverTask ← IO.asTask (Runtime.run e serverProg) _root_.Task.Priority.dedicated
  let addr ← Runtime.Listener.sockName l
  let client ← Std.Async.Async.block do
    let c ← Std.Async.TCP.Socket.Client.mk
    c.connect addr
    return c
  let started? ← IO.wait (IO.Promise.result? started)
  if started?.isNone then
    IO.eprintln "drainDeadline: handler never started"
    return 1
  let t0 ← IO.monoNanosNow
  e.stop
  let outer : Except IO.Error (Except IO.Error Unit) ← IO.wait serverTask
  let elapsedMs := ((← IO.monoNanosNow) - t0) / 1000000
  let _ := client
  let aborted := match ← outcome.get with | some (.aborted _) => true | _ => false
  let exitCount ← exits.get
  Runtime.Io.stop
  match outer with
  | Except.error e => IO.eprintln s!"drainDeadline: driver failed: {e}"; return 1
  | Except.ok (.error e) => IO.eprintln s!"drainDeadline: loop failed: {e}"; return 1
  | Except.ok (.ok ()) =>
    IO.println s!"drainDeadline|returned=yes|aborted={aborted}|exits={exitCount}|elapsedMs={elapsedMs}"
    if aborted && exitCount == 1 && elapsedMs < 1000 then return 0 else return 1
