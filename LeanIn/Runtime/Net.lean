import Std
import Std.Async.TCP
import LeanIn.Runtime.Leaf
import LeanIn.Task.Basic

/-!
# Sockets on our carriers

`interface.md` §4: the leaf operations stay in `Std.Async` and are reached across W1's seam. This file is the
socket half of that seam — and the accept loop, which `Std.Http.Server` cannot give us. Its own loop runs as a
stock `Task` (`Server.lean:193`), so a server that has to run on our carriers owns the loop, not only the
leaves; that is W10's finding and W9's deliverable.

Every operation below is `Std.Async`'s, awaited through `awaitAsync`, so a completion enqueues our resume and
nothing of ours runs on the thread that completed the socket operation.

**Nothing here is opened from `Std.Async`, and that is deliberate.** Two of its names collide with ours — it has
its own `MonadAsync`, with `async` where ours has `spawn`, and its own `background` — so this module qualifies
every name on the far side of the seam and leaves ours unqualified. The file is the boundary, and it reads like
one.

**What is deliberately not here.** A transport class. `Std.Http.Transport` is `Std.Async.Async`-typed, so an
instance over these wrappers would hand a driver a stock-typed value and put the work back on the pool; the
class belongs with the layer that drives it, and that layer is the copy W15 describes.

**Errors.** A socket failure panics, because `interface.md` §5 has no error channel on a task and `Leaf.lean`
says so loudly rather than leaving an awaiter parked. End of stream is `none` from `recv` and not an error,
which is the case a server meets every time a client goes away; giving failures somewhere to go is W5.
-/

namespace LeanIn.Runtime

/-- A listening socket whose operations come back as *our* computations. -/
structure Listener where
  srv : Std.Async.TCP.Socket.Server

/-- Bind and listen. Port `0` asks the OS for an ephemeral one, which `sockName` then reports — binding before
anything is served, so a client that connects immediately meets a listening socket rather than a race. -/
def Listener.bind (addr : Std.Net.SocketAddress) (backlog : UInt32 := 1024) : IO Listener := do
  let srv ← Std.Async.TCP.Socket.Server.mk
  srv.bind addr
  srv.listen backlog
  srv.noDelay
  return ⟨srv⟩

/-- The address actually bound, which is what a client needs when the port was ephemeral. -/
def Listener.sockName (l : Listener) : IO Std.Net.SocketAddress :=
  l.srv.getSockName

/-- **Accept, awaited as one of ours.** -/
def Listener.accept (l : Listener) (hooks : Hooks) : Task.Async (Std.Async.TCP.Socket.Client) :=
  awaitAsync hooks l.srv.accept

/-- A connected socket: the four operations a connection loop needs. -/
abbrev Conn := Std.Async.TCP.Socket.Client

/-- Receive up to `size` bytes. `none` is end of stream. -/
def Conn.recv (c : Conn) (hooks : Hooks) (size : UInt64 := 65536) : Task.Async (Option ByteArray) :=
  awaitAsync hooks (Std.Async.TCP.Socket.Client.recv? c size)

/-- Send one buffer. -/
def Conn.send (c : Conn) (hooks : Hooks) (data : ByteArray) : Task.Async Unit :=
  awaitAsync hooks (Std.Async.TCP.Socket.Client.send c data)

/-- Send several buffers as one operation. -/
def Conn.sendAll (c : Conn) (hooks : Hooks) (data : Array ByteArray) : Task.Async Unit :=
  awaitAsync hooks (Std.Async.TCP.Socket.Client.sendAll c data)

/-- Shut down the write side: how a server says it is done with a connection. -/
def Conn.shutdown (c : Conn) (hooks : Hooks) : Task.Async Unit :=
  awaitAsync hooks (Std.Async.TCP.Socket.Client.shutdown c)

/-- **Echo a connection until the peer stops, then shut it down.**

`partial` because a connection has no bound, and `Async` is `Inhabited` — which is what lets this be recursion
rather than a `while` in a monad with no way to say it terminates. -/
partial def echoConn (hooks : Hooks) (c : Conn) : Task.Async Unit := do
  match ← c.recv hooks with
  | none       => c.shutdown hooks
  | some chunk => c.send hooks chunk; echoConn hooks c

/-- **An accept loop of our own.** It accepts `n` connections — one task each, through `background`, which
against `MonadAsync` is the local route, so a connection stays on the carrier its accept ran on — and then
awaits them all.

Awaiting is what makes "the executor holds nothing afterwards" an observation rather than a guess, so this is
the loop the scenario uses. A fire-and-forget variant existed here and was deleted rather than kept: nothing
called it, and an untested export is worse than a missing one, since the driver that will want it can add it
back where it is used. -/
def serveNJoin (hooks : Hooks) (l : Listener) (n : Nat) (body : Conn → Task.Async Unit) : Task.Async Unit := do
  let hs ← (List.range n).mapM (fun _ => do
    let client ← l.accept hooks
    Task.MonadAsync.spawn (body client))
  hs.forM (fun h => Task.MonadAwait.await h)

/-- **The loopback address a scenario binds**: `127.0.0.1` and a port. -/
def loopback (port : UInt16 := 0) : Std.Net.SocketAddress :=
  .v4 ⟨⟨#v[127, 0, 0, 1]⟩, port⟩

end LeanIn.Runtime
