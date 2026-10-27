module

import Std

import LeanIn
import LeanIn.Runtime.Net
import LeanIn.Http.Server

/-!
# A streaming HTTP echo on `leanin`'s runtime

Run it with `lake exe streamEcho [port]`. Unlike `server`, the handler reads the request body and writes the
response body incrementally: neither direction is accumulated, and the response is `Transfer-Encoding: chunked`
on HTTP/1.1. A `POST` echoes each body chunk as it arrives; any other method answers one fixed chunk.
-/

open LeanIn
open LeanIn.Http

namespace LeanIn.Exe.StreamEcho

/-- Echo the request body chunk by chunk, then terminate the chunked response. -/
partial def echoBody (body : Server.BodyReader) (w : Server.ResponseWriter) : Runtime.VM Unit := do
  match ← body.recv 65536 with
  | some chunk =>
    w.write chunk
    echoBody body w
  | none => w.finish

/-- `POST` streams; everything else answers one chunk. `/slow` parks in a sleep that the configured
scope cancellation aborts after 50 ms, so the connection ends with no response. -/
def handler (clock : Runtime.Clock) : Server.StreamHandler := fun head body w => do
  if H1.expectsContinue head then
    w.sendContinue
    w.start { status := 200, reason := "OK" }
    w.write "continued\n".toUTF8
    w.finish
  else if head.targetString? == some "/hints" then
    w.interim { status := 103, reason := "Early Hints" }
    w.start { status := 200, reason := "OK" }
    w.write "hinted\n".toUTF8
    w.finish
  else if head.targetString? == some "/slow" then
    Runtime.VM.sleep clock 60000
    w.start { status := 200, reason := "OK" }
    w.finish
  else
    w.start { status := 200, reason := "OK" }
    if head.method == H1.Method.post then
      echoBody body w
    else
      w.write "hello\n".toUTF8
      w.finish

end LeanIn.Exe.StreamEcho

open LeanIn.Exe.StreamEcho

public def main (args : List String) : IO UInt32 := do
  let port : UInt16 :=
    match args with
    | p :: _ => (p.toNat?.getD 8790).toUInt16
    | [] => 8790
  let hooks ← Runtime.Hooks.new
  let l ← Runtime.Listener.bind (Runtime.loopback port)
  let addr ← Runtime.Listener.sockName l
  let e ← Sched.Executor.new LeanIn.Task.Item 256 1
  let clock := Runtime.Clock.live hooks
  let cfg : Server.Config :=
    { clock
      -- The streaming echo is the case for bodies past the buffered default; the test also checks
      -- that this configured ceiling is enforced with a 413.
      h1 := { maxBody := 4 * 1024 * 1024 }
      continuePolicy := .application
      onScope := fun head scope => do
        if head.targetString? == some "/slow" then
          let _ ← IO.asTask (do
            IO.sleep 50
            Runtime.Scope.cancelNow scope) _root_.Task.Priority.dedicated
          pure () }
  IO.println s!"leanin stream server listening on {addr}"
  let prog : LeanIn.Task.EAsync IO.Error Unit :=
    Runtime.serveForever hooks l (fun c => Server.serveConnStream cfg c (handler clock))
  let outcome : Except IO.Error Unit ← Runtime.run e prog
  Runtime.Io.stop
  match outcome with
  | .ok _ => return 0
  | .error err =>
    IO.println s!"the accept loop ended: {err}"
    return 1
