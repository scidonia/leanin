module

import LeanIn
import LeanIn.Http.Compat

/-- A stock handler: read the request body, echo it, and add one response header. -/
def stockEcho : Std.Http.Server.Handler Unit :=
  Std.Http.Server.Handler.mk Std.Http.Body.Full (fun _ req => do
    let body ← Std.Http.Body.Stream.readAll (α := ByteArray) (m := Std.Async.ContextAsync) req.body
    let full ← Std.Http.Body.Full.ofByteArray body
    let name := (Std.Http.Header.Name.ofString? "x-stock").getD Std.Http.Header.Name.host
    let value := (Std.Http.Header.Value.ofString? "yes").getD (Std.Http.Header.Value.mk "yes")
    let headers := Std.Http.Headers.empty.insert name value
    return { line := { status := .ok, headers }, body := full })
    (fun _ _ => pure ()) (fun _ _ => pure true)

public def main : IO UInt32 := do
  let raw := "POST /echo HTTP/1.1\r\nHost: x\r\nContent-Length: 5\r\n\r\n".toUTF8
  match LeanIn.Http.H1.parseHead raw 0 {} with
  | .ok head _ =>
      let adapted := LeanIn.Http.Compat.ofStock stockEcho ()
      let out ← IO.mkRef (none : Option (LeanIn.Http.H1.ResponseHead × ByteArray))
      LeanIn.Runtime.VM.runAsync (adapted head "hello".toUTF8) (fun v => out.set (some v))
      match ← out.get with
      | some (rh, body) =>
          let hasHeader := rh.headers.any (fun (n, v) => n == "x-stock" && v == "yes")
          let ok := rh.status == 200 && body == "hello".toUTF8 && hasHeader
          let bodyText := (String.fromUTF8? body).getD ""
          IO.println s!"compat|status={rh.status}|body={bodyText}|x-stock={hasHeader}|ok={ok}"
          return if ok then 0 else 1
      | none =>
          IO.eprintln "compat: adapter produced no response"
          return 1
  | _ =>
      IO.eprintln "compat: failed to parse the probe head"
      return 1
