import Std
import Std.Async.TCP
import LeanIn.Runtime.Leaf
import LeanIn.Runtime.Time
import LeanIn.Task.Error
import LeanIn.Task.Registry
import LeanIn.Task.Sync

/-!
# Sockets on our carriers

`interface.md` §4: the leaf operations stay in `Std.Async` and are reached across W1's seam. This file is the
socket half of that seam — and the accept loop, which `Std.Http.Server` cannot give us. Its own loop runs as a
stock `Task` (`Server.lean:193`), so a server that has to run on our carriers owns the loop, not only the
leaves; that is W10's finding and W9's deliverable.

Every operation below is `Std.Async`'s, awaited through W1's seam, so a completion enqueues our resume and
nothing of ours runs on the thread that completed the socket operation.

**Nothing here is opened from `Std.Async`, and that is deliberate.** Two of its names collide with ours — it has
its own `MonadAsync`, with `async` where ours has `spawn`, and its own `background` — so this module qualifies
every name on the far side of the seam and leaves ours unqualified. The file is the boundary, and it reads like
one.

**Every operation returns a failure rather than raising it.** This is the first place `EAsync` is the right
answer rather than a convenience: a client that closes a connection mid-request, or a socket that reports ECONNRESET,
is the *normal* case for a server, so these wrappers convert through `awaitAsyncE` and the error travels with
the value. A panic here would take the process down for an event a server meets every day. -/

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

/-- **Accept, awaited as one of ours.** A failing accept is a value: a listener that has been closed is not an
abort. -/
def Listener.accept (l : Listener) (hooks : Hooks) : Task.EAsync IO.Error (Std.Async.TCP.Socket.Client) :=
  awaitAsyncE hooks l.srv.accept

/-- A connected socket: the four operations a connection loop needs. -/
abbrev Conn := Std.Async.TCP.Socket.Client

/-- Receive up to `size` bytes. `none` is end of stream, which is not a failure. -/
def Conn.recv (c : Conn) (hooks : Hooks) (size : UInt64 := 65536) : Task.EAsync IO.Error (Option ByteArray) :=
  awaitAsyncE hooks (Std.Async.TCP.Socket.Client.recv? c size)

/-- Send one buffer. -/
def Conn.send (c : Conn) (hooks : Hooks) (data : ByteArray) : Task.EAsync IO.Error Unit :=
  awaitAsyncE hooks (Std.Async.TCP.Socket.Client.send c data)

/-- Send several buffers as one operation. -/
def Conn.sendAll (c : Conn) (hooks : Hooks) (data : Array ByteArray) : Task.EAsync IO.Error Unit :=
  awaitAsyncE hooks (Std.Async.TCP.Socket.Client.sendAll c data)

/-- Shut down the write side: how a server says it is done with a connection. -/
def Conn.shutdown (c : Conn) (hooks : Hooks) : Task.EAsync IO.Error Unit :=
  awaitAsyncE hooks (Std.Async.TCP.Socket.Client.shutdown c)

/-- **Connect, awaited as one of ours.** A client operation, and the one the error channel's own test needs: a
refused connect is the ordinary way to make a socket operation fail on purpose.

The socket is made through `ofAsync`/`ofIO` rather than by lifting the `IO` action implicitly: do-notation
inserts a lift for a nested action but not for a bind here, so the two steps are written out. -/
def connect (hooks : Hooks) (addr : Std.Net.SocketAddress) : Task.EAsync IO.Error Conn := do
  let c ← Task.EAsync.ofAsync (Task.Async.ofIO Std.Async.TCP.Socket.Client.mk)
  let _ ← awaitAsyncE hooks (Std.Async.TCP.Socket.Client.connect c addr)
  return c

/-- **Echo a connection until the peer stops, then shut it down.**

A socket failure ends the connection rather than the loop: the peer going away mid-stream is the case this
signature exists for, and the alternative — what the first version of this file did — is a process that dies
because a client closed a socket.

`partial` because a connection has no bound, and `Async` is `Inhabited`, which is what lets this be recursion
rather than a `while` in a monad with no way to say it terminates. -/
partial def echoConn (hooks : Hooks) (c : Conn) : Task.EAsync IO.Error Unit := do
  try
    match ← Conn.recv c hooks with
    | none      => Conn.shutdown c hooks
    | some ch   => Conn.send c hooks ch; echoConn hooks c
  catch _ => pure ()

/-- **An accept loop of our own.** It accepts `n` connections — one task each, through `background`, which
against `MonadAsync` is the local route, so a connection stays on the carrier its accept ran on — and then
awaits them all.

Awaiting is what makes "the executor holds nothing afterwards" an observation rather than a guess, so this is
the loop the scenario uses. A fire-and-forget variant existed here and was deleted rather than kept: nothing
called it, and an untested export is worse than a missing one, since the driver that will want it can add it
back where it is used. -/
def serveNJoin (hooks : Hooks) (l : Listener) (n : Nat) (body : Conn → Task.EAsync IO.Error Unit) :
    Task.EAsync IO.Error Unit := do
  let reg : Task.Registry (Except IO.Error Unit) ← monadLift (Task.Registry.new (α := Except IO.Error Unit))
  for _ in List.range n do
    let client ← Listener.accept l hooks
    let h ← Task.MonadAsync.spawn (body client)
    monadLift (Task.Registry.add reg h)
  Task.EAsync.ofAsync (Task.Registry.joinAll reg)

/-- The accept-until-stop loop of `serveUntilStopped`: one attempt per iteration, with the accepted connection's
handle registered in a `Registry`, until `Executor.isStopping` — then `Registry.drain` awaits everything still
registered, so the stop is a drain *operation* rather than a `List.forM` in the loop. -/
private partial def serveUntilStoppedLoop (hooks : Hooks) (e : Sched.Executor Task.Item cap) (l : Listener)
    (interval : Std.Time.Millisecond.Offset) (body : Conn → Task.EAsync IO.Error Unit)
    (reg : Task.Registry (Except IO.Error Unit)) : Task.EAsync IO.Error Unit := do
  if ← monadLift (e.isStopping : IO Bool) then
    Task.EAsync.ofAsync (Task.Registry.drain reg)
  else
    match ← monadLift (Std.Async.TCP.Socket.Server.tryAccept l.srv : IO (Option Conn)) with
    | some client =>
      let h ← Task.MonadAsync.spawn (body client)
      monadLift (Task.Registry.add reg h)
      serveUntilStoppedLoop hooks e l interval body reg
    | none =>
      Task.EAsync.ofAsync (sleep hooks interval)
      serveUntilStoppedLoop hooks e l interval body reg

/-- **Accept until the executor is stopping, then finish what is in flight and return.**

A drain in the shape W5 asks for: stop accepting, let the connections already accepted run to completion, and
return only *after* awaiting them — so a driver returns with nothing held rather than with work it will never
run. It takes the executor because the decision it makes is the executor's own flag; `Executor.isStopping` is the
reading, and there is no second copy of it here. The outstanding handles are a `Registry`; the stop is
`Registry.drain`, which takes the membership, clears it, and awaits each handle *outside* the lock.

The trailing `hs` parameter is the loop's initial membership, kept so the signature is unchanged; callers pass
`[]`, and it is seeded into the registry once, at entry, before the loop runs.

**It is exercised, and by a scenario rather than a diagnostic.** The first version of the diagnostic for this loop
— connect, send, stop, read — hung, and the hang was the driver's rather than the loop's: `blockOn` ended as soon
as the pool was empty and the executor was stopping, which abandons a continuation registered on a leaf. Fixed
there, `tests/executor-contract.sh SC10` runs this loop to completion and reads `served=1 echoed=yes
inFlightAfter=0 pendingHooks=0`.

**Polling is the cost, and it is W7's absence showing through.** `tryAccept` is a non-blocking leaf, so the loop
sleeps `interval` between attempts instead of parking on a selector. The accept-versus-shutdown choice is
exactly a `select`, the interface has none yet, and the price of not having it is a drain whose latency is one
poll interval rather than immediate. -/
def serveUntilStopped (hooks : Hooks) (e : Sched.Executor Task.Item cap) (l : Listener)
    (interval : Std.Time.Millisecond.Offset) (body : Conn → Task.EAsync IO.Error Unit)
    (hs : List (Task.Task (Except IO.Error Unit))) : Task.EAsync IO.Error Unit := do
  let reg : Task.Registry (Except IO.Error Unit) ← monadLift (Task.Registry.new (α := Except IO.Error Unit))
  monadLift (hs.forM (fun h => Task.Registry.add reg h))
  serveUntilStoppedLoop hooks e l interval body reg

/-- The admission loop of `serveBounded`: one admission per iteration, with the handles accepted so
far accumulated, until exactly `n` connections have been served — then every handle is awaited.

A permit is taken before the accept and never after it. `tryAcquire` first, because a free permit must
not pay for a park that would wake it at once; `acquire` only when the bound is full, which parks this
step and resumes it holding the permit, so the accept below always runs with one. A failing accept
releases the permit it was holding before the failure travels, so no failure path can drain the bound. -/
private partial def serveBoundedLoop (hooks : Hooks) (l : Listener) (sem : Task.Sync.Semaphore)
    (serve : Conn → Task.EAsync IO.Error Unit) (i n : Nat)
    (reg : Task.Registry (Except IO.Error Unit)) : Task.EAsync IO.Error Unit := do
  if i ≥ n then
    Task.EAsync.ofAsync (Task.Registry.drain reg)
  else
    if ← monadLift (Task.Sync.Semaphore.tryAcquire sem) then pure ()
    else Task.EAsync.ofAsync (Task.Sync.Semaphore.acquire sem)
    let client ← try
      Listener.accept l hooks
    catch e =>
      monadLift (Task.Sync.Semaphore.release sem)
      throw e
    let h ← Task.MonadAsync.spawn (serve client)
    monadLift (Task.Registry.add reg h)
    serveBoundedLoop hooks l sem serve (i + 1) n reg

/-- **An accept loop with an admission bound.** It serves exactly `n` connections while admitting at
most `bound` at a time: with the bound full the loop parks on the semaphore rather than admitting, and
a connection's permit is released when its body ends, so a place in the bound is returned by every
route out of a body.

That release is the point, and it is total. The body runs under a `try`; its own `release` is the
tail of the `try`, and the branch releases and rethrows. `EAsync`'s sequencing short-circuits on
`error`, so the tail runs exactly when the body returned and the branch exactly when the body failed
— one release on every path a body can take, none skipped, including the failure. That total is over
the body's own return and failure paths only: under cancellation `Item.fire` skips the whole step, so
the release is skipped too — the limit `decisions.md` D15 records. The accepted
connection's own failure is the ordinary case here (`echoConn`'s comment), so a body returning
`.error` must give its permit back rather than leaking it; a leak would only *reduce* admissions and
so never break the bound, but it would degrade the bound to a hint.

Every handle is awaited before the function returns (the shape `serveNJoin` has), so a driver returns
with nothing held. The signature matches `serveNJoin`'s, so a caller moves between the two loops by
changing one line; the loop assigns no connection id, so the payload id a body reads is the client's
and an admission ordinal can never be confused with a connection identity.

The semaphore is the right primitive and not merely an available one: the bound is the service's own
obligation, and `Task.Sync.Semaphore` is built for this shape — a wake is a hint and a permit is taken
in the waiter's own step, so the loop can never be handed a permit it then skips. -/
def serveBounded (hooks : Hooks) (l : Listener) (bound : Nat) (n : Nat)
    (body : Conn → Task.EAsync IO.Error Unit) : Task.EAsync IO.Error Unit := do
  let sem ← monadLift (Task.Sync.Semaphore.new bound)
  let serve (c : Conn) : Task.EAsync IO.Error Unit := do
    try
      body c
      monadLift (Task.Sync.Semaphore.release sem)
    catch e =>
      monadLift (Task.Sync.Semaphore.release sem)
      throw e
  let reg : Task.Registry (Except IO.Error Unit) ← monadLift (Task.Registry.new (α := Except IO.Error Unit))
  serveBoundedLoop hooks l sem serve 0 n reg

/-- **The loopback address a scenario binds**: `127.0.0.1` and a port. -/
def loopback (port : UInt16 := 0) : Std.Net.SocketAddress :=
  .v4 ⟨⟨#v[127, 0, 0, 1]⟩, port⟩

end LeanIn.Runtime
