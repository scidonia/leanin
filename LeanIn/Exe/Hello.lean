module

public import LeanIn
public import LeanIn.Async

public section

/-!
# A compiled hello-world server

`lake exe hello [port]` binds the loopback port, serves every connection with a compiled accept loop, and
answers each request through compiled per-connection machines. It shows a deadline read, two spawned children
selected by first completion (with timers deciding the race), a response, a close whose refusal is reported,
and a keep-alive loop that recurses on the same connection. Everything runs on the runtime's own primitives:
no `Std.Http.Server` and no stock `Task` in the serving path.

Every suspension is one of the classified effects: the accept parks on the listener's cell, the read and the
write park on the connection, and the spawn schedules the connection machine as an executor item through the
same inject that wakes the driver.
-/

open LeanIn

/-- A response with the body's length and, when asked, `Connection: close`. -/
def response (body : ByteArray) (close : Bool) : ByteArray :=
  let connection := if close then "Connection: close\r\n" else ""
  s!"HTTP/1.1 200 OK\r\n{connection}Content-Length: {body.size}\r\n\r\n".toUTF8 ++ body

-- A child machine: sleep for `d`, then deliver `payload`. The connection is carried because the spawn surface
-- takes one, and is otherwise unused.
async def helloAfter (c : LeanIn.Runtime.Conn) (clock : LeanIn.Runtime.Clock)
    (d : Std.Time.Millisecond.Offset) (payload : ByteArray) : ByteArray := do
  await (LeanIn.Runtime.Io.sleepRaw clock.schedule d)
  return payload

-- The content of one answer: spawn two children at different delays and select the first to finish. This is the
-- spawn/join/select/timer shape; the loser still finishes and its cell is simply never awaited.
async def helloBody (c : LeanIn.Runtime.Conn) (push : LeanIn.Task.Item → BaseIO Unit)
    (clock : LeanIn.Runtime.Clock) : ByteArray := do
  let hFast : LeanIn.Runtime.RawCell (Except IO.Error ByteArray) :=
    await (helloAfter.spawn push c clock 1 "hello".toUTF8)
  let hSlow : LeanIn.Runtime.RawCell (Except IO.Error ByteArray) :=
    await (helloAfter.spawn push c clock 25 "slow".toUTF8)
  let winner : Nat × Except IO.Error ByteArray := await (LeanIn.Runtime.selectRaw hFast hSlow)
  match winner.2 with
  | .ok body => return body
  | .error e => throw e

-- Read a request with a deadline. A stall, end of stream and a transport failure all end the connection.
async def readRequest (c : LeanIn.Runtime.Conn) (clock : LeanIn.Runtime.Clock) :
    Option ByteArray := do
  let rt := await (LeanIn.Runtime.Io.recvTimeoutRaw c clock.schedule 5000 65536)
  match rt with
  | none => return none
  | some (.ok none) => return none
  | some (.ok (some bs)) => return some bs
  | some (.error e) =>
      let closed := await (LeanIn.Runtime.Io.closeRaw c)
      if closed then throw e else throw (IO.userError s!"{e}; and the loop refused the close")

-- One connection's work: read, build the body through spawned children, answer, close, and report the close.
async def helloConn (c : LeanIn.Runtime.Conn) (push : LeanIn.Task.Item → BaseIO Unit)
    (clock : LeanIn.Runtime.Clock) : Unit := do
  let req : Option ByteArray := await (readRequest.run c clock)
  match req with
  | none =>
      let closed := await (LeanIn.Runtime.Io.closeRaw c)
      if closed then return () else throw (IO.userError "helloConn: the loop refused the close")
  | some _ =>
      let body := await (helloBody.run c push clock)
      await (LeanIn.Runtime.Io.sendAllRaw c #[response body true])
      let closed := await (LeanIn.Runtime.Io.closeRaw c)
      if closed then return () else throw (IO.userError "helloConn: the loop refused the close")

-- A keep-alive connection loop: read, answer, and recurse on the same connection.
async def helloKeep (c : LeanIn.Runtime.Conn) (push : LeanIn.Task.Item → BaseIO Unit)
    (clock : LeanIn.Runtime.Clock) : Unit := do
  let req : Option ByteArray := await (readRequest.run c clock)
  match req with
  | none =>
      let closed := await (LeanIn.Runtime.Io.closeRaw c)
      if closed then return () else throw (IO.userError "helloKeep: the loop refused the close")
  | some _ =>
      let body := await (helloBody.run c push clock)
      await (LeanIn.Runtime.Io.sendAllRaw c #[response body false])
      recurse

-- The accept loop: one connection at a time, its handler spawned as an executor item, then recurse. The
-- listener, the inject and the mode are the loop's carried state; an accept failure ends the loop loudly.
async def helloServe (l : LeanIn.Runtime.Listener) (push : LeanIn.Task.Item → BaseIO Unit)
    (clock : LeanIn.Runtime.Clock) (keep : Bool) : Unit := do
  let c : Except IO.Error LeanIn.Runtime.Conn := await (LeanIn.Runtime.Io.acceptRaw l push)
  match c with
  | .error e =>
    throw e
  | .ok conn =>
    -- Handlers are unsupervised here: the handle is discarded deliberately. A connection's failure is
    -- confined to that connection by the handler's own policy, and the loop's only terminal is an accept the
    -- listener can no longer complete — which is what reaches the run's continuation and `main`.
    if keep then
      await (helloKeep.spawn push conn push clock)
      recurse
    else
      await (helloConn.spawn push conn push clock)
      recurse

def main (args : List String) : IO UInt32 := do
  let port := (args.head?.bind (·.toNat?)).getD 8085
  let keep := args.getD 1 "close" == "keep"
  let l ← LeanIn.Runtime.Listener.bind (LeanIn.Runtime.loopback port.toUInt16)
  let e ← LeanIn.Sched.Executor.new LeanIn.Task.Item 256 1
  let push := LeanIn.Runtime.sharedPush e
  let clock := LeanIn.Runtime.Clock.live (← LeanIn.Runtime.Hooks.new)
  let addr ← LeanIn.Runtime.Listener.sockName l
  IO.println s!"hello listening on {addr}"
  (← IO.getStdout).flush
  -- The compiled loop owns the connection; only its terminal — an accept the loop can no longer complete —
  -- reaches the wrapper's continuation, which is what lets `main` report it.
  match (← (LeanIn.Runtime.run e (helloServe l push clock keep) : IO (Except IO.Error Unit))) with
  | .ok () => return 0
  | .error e =>
    IO.eprintln s!"hello: {e}"
    return 1

end
