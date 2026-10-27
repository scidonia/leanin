module

import Std.Http.Server
import Std.Http.Data.Body
import Std.Async
open Std.Http Std.Async

/-- The same response shape as the leanin and Node servers, via the shipped `Std.Http.Server`. -/
def helloBody (head : Request.Head) : ByteArray :=
  s!"hello from std\nmethod={head.method} path={head.uri} version={head.version}\n".toUTF8

public def main (args : List String) : IO UInt32 := do
  let port := (args.head?.bind (·.toNat?)).getD 8090
  let addr : Std.Net.SocketAddress := .v4 { addr := Std.Net.IPv4Addr.ofParts 127 0 0 1, port := port.toUInt16 }
  let handler := Server.Handler.ofFn fun (req : Request Body.Stream) => do
    let body := helloBody req.line
    let fullBody ← Body.Full.ofByteArray body
    return Response.ok
      |>.header! "Content-Length" (toString body.size)
      |>.body (Body.Any.ofBody fullBody)
  -- `maxRequests` bumped far past the default 100 so keep-alive is not closed mid-benchmark (like the others).
  let _serverTask ← Async.toIO (Server.serve addr handler { maxRequests := 1000000000 })
  IO.sleep 3600000
  return 0
