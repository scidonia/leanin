module

import LeanIn
import LeanIn.Async

/-!
# A two-connection relay, for the compiled surface's operand test

`lake exe asyncRelay <port>` binds one listener, accepts two connections in order, and runs a compiled
machine that reads exactly seven bytes from the first and writes them to the second. The two sockets
are distinguishable and the read size is not the default, so the socket-level observation separates the
author's operands from the carried machine parameter.
-/

open LeanIn

/-- Read seven bytes from `src`, write them to `dst`, and close `dst`. The two connections are separate
parameters: `src` is the machine's carried value, `dst` is threaded through the generated state. -/
async def relay (src : Runtime.Conn) (dst : Runtime.Conn) : Unit := do
  let chunk := await (LeanIn.Runtime.Io.recvRaw src 7)
  await (LeanIn.Runtime.Io.sendRaw dst chunk)
  let closed := await (LeanIn.Runtime.Io.closeRaw dst)
  if closed then return () else throw (IO.userError "relay: the loop refused the close")

public def main (args : List String) : IO UInt32 := do
  let port : UInt16 := ((args.headD "8795").toNat?.getD 8795).toUInt16
  let hooks ← Runtime.Hooks.new
  let l ← Runtime.Listener.bind (Runtime.loopback port)
  let e ← Sched.Executor.new LeanIn.Task.Item 256 1
  let prog : LeanIn.Task.EAsync IO.Error (Runtime.Conn × Runtime.Conn) := do
    let src ← Runtime.Listener.accept l hooks
    let dst ← Runtime.Listener.accept l hooks
    pure (src, dst)
  let (src, dst) ← match ← Runtime.run e prog with
    | .ok pair => pure pair
    | .error e => IO.eprintln s!"relay: accept failed: {e}"; return 1
  let outcome ← Runtime.run e (relay src dst)
  Runtime.Io.stop
  match outcome with
  | .ok () => return 0
  | .error e => IO.eprintln s!"relay: {e}"; return 1
