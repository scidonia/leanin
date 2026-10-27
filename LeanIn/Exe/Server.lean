module

import Std

import LeanIn
import LeanIn.Runtime.Net
import LeanIn.Http.Server

/-!
# An HTTP server on `leanin`'s runtime

Run it with `lake exe server [port]` — the port defaults to 8080. It binds the loopback address, prints the
address it took, and serves every connection on an executor of our own, driving `LeanIn.Http.H1`'s pure machine
through `LeanIn.Http.Server.serveConn` — a per-connection state machine compiled by `async`. The protocol is
ours as well (parsing, framing, keep-alive and the limits live in `LeanIn.Http.H1`), and the driver, the accept
loop and every await are ours, so a handler runs on one of our carriers rather than on the stock `Task` pool.

`Runtime.serveUntilStopped` is the accept loop. It polls a non-blocking `tryAccept` between sleeps because the
interface has no selector yet, so a stop drains at one poll interval's latency rather than immediately; that
absence is recorded in the runtime's own docstring as W7's, not hidden here.
-/

open LeanIn
open LeanIn.Http

/-- The reply to any request: the method, path and version echoed back in a small body. -/
def reply (head : H1.Head) : H1.ResponseHead × ByteArray :=
  let body :=
    s!"hello from leanin\nmethod={head.method} path={head.targetString} version={head.version}\n".toUTF8
  let headers := #[("Content-Length", toString body.size)]
  ({ status := 200, reason := "OK", headers }, body)

/-- Report the counters the executor already keeps, every 20 000 requests. `taken` is cumulative items served —
every worker's pool plus the shared cell's — so `taken / requests` is the number of scheduling round-trips one
request costs. Nothing on the hot path is instrumented but one `IO.Ref` bump. -/
def reportMetrics (e : Sched.Executor LeanIn.Task.Item 256) (hooks : Runtime.Hooks)
    (served : IO.Ref Nat) (t0 : Nat) : IO Unit := do
  let n ← served.modifyGet fun n => (n + 1, n + 1)
  if n % 20000 == 0 then
    let s ← e.snapshot
    let fired := ((← e.metrics).getD []).map (fun (cc : Sched.CarrierCounters) => cc.fired) |>.sum
    let pend ← Runtime.pending hooks
    let t ← IO.monoNanosNow
    IO.println s!"metrics|requests={n}|taken={s.taken}|takenMilliPerReq={(s.taken * 1000) / n}|fired={fired}|held={s.held}|pending={pend}|nsPerReq={(t - t0) / n}"

public def main (args : List String) : IO UInt32 := do
  let port : UInt16 :=
    match args with
    | p :: _ => (p.toNat?.getD 8080).toUInt16
    | [] => 8080
  let hooks ← Runtime.Hooks.new
  let l ← Runtime.Listener.bind (Runtime.loopback port)
  let addr ← Runtime.Listener.sockName l
  let workers :=
    args.findSome? (fun a => (a.dropPrefix? "workers=").bind (fun n => n.toNat?)) |>.getD 1
  let e ← Sched.Executor.new LeanIn.Task.Item 256 workers
  let bigstall := args.contains "bigstall"
  -- `maxMessages` bumped far past the default 100 so keep-alive is not closed mid-benchmark, as the client
  -- harness (one connection, sequential keep-alive) would otherwise measure only the first 100 exchanges.
  let cfg : LeanIn.Http.Server.Config :=
    { h1 := { maxMessages := 1000000000 }, clock := Runtime.Clock.live hooks,
      stallTimeout := if bigstall then 3600000 else 12000 }
  let quiet := args.contains "quiet"
  -- `metrics` reports, every 20 000 requests, the counters the executor already keeps: `taken` is cumulative
  -- items served (every worker's pool plus the shared cell), so `taken / requests` is the number of scheduling
  -- round-trips one request costs. Nothing on the hot path is instrumented — one `IO.Ref` bump per request.
  let metrics := args.contains "metrics"
  let served ← IO.mkRef (0 : Nat)
  let metricsT0 ← IO.monoNanosNow
  -- `static` answers with a response built once, so a measurement separates this runtime's cost from the cost of
  -- formatting the echoed body per request.
  let static := args.contains "static"
  let staticBody : ByteArray := "hello from leanin\nmethod=GET path=/bench version=HTTP/1.1\n".toUTF8
  let staticHead : H1.ResponseHead :=
    { status := 200, reason := "OK", headers := #[("Content-Length", toString staticBody.size)] }
  let handler : LeanIn.Http.Server.Handler := fun head _body => do
    if metrics then
      monadLift (reportMetrics e hooks served metricsT0)
    if static then
      return (staticHead, staticBody)
    if quiet then
      pure ()
    else
      let tid ← monadLift (IO.getTID : IO UInt64)
      monadLift (IO.println s!"  {head.method} {head.targetString} -> 200, on carrier {tid}")
    return reply head
  IO.println s!"leanin server listening on {addr}"
  -- `count=N` serves exactly N connections and then exits: the finite workload a profiler needs, so the process
  -- writes one complete profile instead of being killed mid-run.
  let count? := args.findSome? (fun a =>
    (a.dropPrefix? "count=").bind (fun n => n.toNat?))
  let body : Runtime.Conn → LeanIn.Task.EAsync IO.Error Unit :=
    fun c => LeanIn.Http.Server.serveConn cfg c handler
  let prog : LeanIn.Task.EAsync IO.Error Unit :=
    match count? with
    | some n => Runtime.serveNJoinShared hooks e l n body
    | none   => Runtime.serveForeverShared hooks e l body
  -- The listener's bind started the pump thread; `runCarriersWait` starts `workers` carriers and waits for
  -- the program while that pump serves the loop. A connection stays on the carrier that took its first step.
  let (_, outcome) ← Runtime.runCarriersWait e workers prog
  Runtime.Io.stop
  match outcome with
  | .ok _ => return 0
  | .error err =>
    IO.println s!"the accept loop ended: {err}"
    return 1
