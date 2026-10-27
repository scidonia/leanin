module

import Std

import LeanIn
import LeanIn.Runtime.Net
import LeanIn.Http.StdHandler

/-!
# A `Std.Http`-shaped handler on `leanin`'s runtime

Run it with `lake exe stdEcho [port]`. The handler is a `StdHandler`: it reads a `Std.Http.Request` and returns
a `Std.Http.Response`. Each request, continue decision and failure notification is printed as a `|`-separated
record on standard output, which `tests/std-handler-contract.sh` reads.

- `/info` answers the method, the target, every `X-Multi` value and the `RemoteAddr` extension.
- `/stream` answers two chunks through a streamed body.
- `/stream-cleanup` streams 4 MiB with a recorded `finally`.
- `/no-content` answers `204` with a body that must not be sent.
- `/stream-short` and `/stream-long` declare a length their producer does not satisfy.
- `/throw` raises.
- `/refuse` is refused by `onContinue`.
- anything else echoes the request body.
-/

open LeanIn
open LeanIn.Http

namespace LeanIn.Exe.StdEcho

/-- Print one record and flush it, so the fixture reads it while the server is still running. -/
def record (s : String) : IO Unit := do
  IO.println s
  (← IO.getStdout).flush

def multiName : Std.Http.Header.Name :=
  (Std.Http.Header.Name.ofString? "x-multi").getD Std.Http.Header.Name.host

def onRequest (req : Std.Http.Request Server.BodyReader) :
    Runtime.VM (Std.Http.Response ResponseBody) := do
  let target := toString req.line.uri
  monadLift (record s!"ran|method={req.line.method}|target={target}")
  if target == "/throw" then
    throw (.userError "boom")
  else if target.startsWith "/info" then
    let multi := ((req.line.headers.getAll? multiName).getD #[]).toList.map (·.value)
    let remote := match req.extensions.get Std.Http.Server.RemoteAddr with
      | some a => toString a
      | none => "none"
    let body := s!"method={req.line.method}|target={target}|x-multi={",".intercalate multi}|remote={remote}\n"
    return { line := { status := .ok }, body := .bytes body.toUTF8 }
  else if target == "/stream" then
    return { line := { status := .ok }, body := .stream none (fun send => do
      send "one\n".toUTF8
      send "two\n".toUTF8) }
  else if target == "/stream-short" then
    return { line := { status := .ok }, body := .stream (some 10) (fun send => send "abc".toUTF8) }
  else if target == "/stream-long" then
    return { line := { status := .ok }, body := .stream (some 3) (fun send => send "abcdef".toUTF8) }
  else if target == "/no-content" then
    return { line := { status := .noContent }, body := .bytes "not sent".toUTF8 }
  else if target == "/stream-cleanup" then
    return { line := { status := .ok }, body := .stream none (fun send => do
      try
        send "one\n".toUTF8
        let chunk := ByteArray.mk (Array.replicate 65536 0x61)
        for _ in List.range 64 do
          send chunk
      finally
        monadLift (record "cleanup|target=/stream-cleanup") ) }
  else
    let body ← req.body.readAll
    return { line := { status := .ok }, body := .bytes body }

def handler : StdHandler where
  onRequest := onRequest
  onFailure := fun e => monadLift (record s!"failure|err={e}")
  onContinue := fun head => do
    let ok := toString head.uri != "/refuse"
    monadLift (record s!"continue|target={head.uri}|ok={ok}")
    return ok

end LeanIn.Exe.StdEcho

open LeanIn.Exe.StdEcho

/-- `--date-check`: `imfFixdate` at instants whose IMF-fixdate `date -u` gives, including a leap day, a century
that is not a leap year, and an instant before the epoch. -/
def dateCheck : IO UInt32 := do
  let cases : List (Int × String) :=
    [(0, "Thu, 01 Jan 1970 00:00:00 GMT"),
     (784111777, "Sun, 06 Nov 1994 08:49:37 GMT"),
     (951782400, "Tue, 29 Feb 2000 00:00:00 GMT"),
     (4107542399, "Sun, 28 Feb 2100 23:59:59 GMT"),
     (-1, "Wed, 31 Dec 1969 23:59:59 GMT")]
  let mut ok := true
  for (secs, want) in cases do
    let got := StdHandler.imfFixdate secs
    record s!"date|secs={secs}|got={got}|ok={got == want}"
    ok := ok && got == want
  record s!"dateCheck|ok={ok}"
  return if ok then 0 else 1

public def main (args : List String) : IO UInt32 := do
  if args == ["--date-check"] then return ← dateCheck
  let port : UInt16 :=
    match args with
    | p :: _ => (p.toNat?.getD 8792).toUInt16
    | [] => 8792
  let hooks ← Runtime.Hooks.new
  let l ← Runtime.Listener.bind (Runtime.loopback port)
  let addr ← Runtime.Listener.sockName l
  let e ← Sched.Executor.new LeanIn.Task.Item 256 1
  let cfg : Server.Config := { clock := Runtime.Clock.live hooks, continuePolicy := .application }
  record s!"listening|addr={addr}"
  let prog : LeanIn.Task.EAsync IO.Error Unit :=
    Runtime.serveForever hooks l (fun c => Server.serveConnStd cfg c handler)
  let outcome : Except IO.Error Unit ← Runtime.run e prog
  Runtime.Io.stop
  match outcome with
  | .ok _ => return 0
  | .error err =>
    IO.println s!"the accept loop ended: {err}"
    return 1
