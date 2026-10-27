module

import Std

import LeanIn
import LeanIn.Runtime.Net
import LeanIn.Http.StdHandler

/-!
# The `Std`-shaped layer against the native handler, at the socket

`lake exe stdBench <port> native|std` serves every request with the same fixed `200` body through the streaming
driver, on one carrier. `native` answers with a `StreamHandler`; `std` answers with a `StdHandler`, so the
difference between the two is the layer: the stock head and header map, the `Request` and `Response`, and the
`Date` header `Std.Http.Server` adds by default. `bench/stdpaired.sh` drives the pair.
-/

open LeanIn
open LeanIn.Http

namespace LeanIn.Exe.StdBench

def body : ByteArray := "hello from leanin\nmethod=GET path=/bench version=HTTP/1.1\n".toUTF8

def native : Server.StreamHandler := fun _ _ w =>
  Server.Stream.respond w { status := 200, reason := "OK" } body

def std : StdHandler where
  onRequest := fun _ => pure { line := { status := .ok }, body := .bytes body }

end LeanIn.Exe.StdBench

open LeanIn.Exe.StdBench

public def main (args : List String) : IO UInt32 := do
  let (port, mode) := match args with
    | p :: m :: _ => ((p.toNat?.getD 8322).toUInt16, m)
    | _ => (8322, "native")
  unless mode == "native" || mode == "std" do
    IO.eprintln "usage: stdBench <port> native|std"
    return 2
  let hooks ← Runtime.Hooks.new
  let l ← Runtime.Listener.bind (Runtime.loopback port)
  let addr ← Runtime.Listener.sockName l
  let e ← Sched.Executor.new LeanIn.Task.Item 256 1
  -- `maxMessages` past the default 100, as `server` does, so keep-alive is not closed mid-run.
  let cfg : Server.Config := { h1 := { maxMessages := 1000000000 }, clock := Runtime.Clock.live hooks, continuePolicy := .application }
  IO.println s!"stdBench {mode} listening on {addr}"
  let serve : Runtime.Conn → LeanIn.Task.EAsync IO.Error Unit :=
    if mode == "std" then fun c => Server.serveConnStd cfg c std
    else fun c => Server.serveConnStream cfg c native
  let (_, outcome) ← Runtime.runCarriersWait e 1 (Runtime.serveForeverShared hooks e l serve)
  Runtime.Io.stop
  match outcome with
  | .ok _ => return 0
  | .error err =>
    IO.println s!"the accept loop ended: {err}"
    return 1
