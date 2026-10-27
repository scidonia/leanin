module

import LeanIn.Runtime.Net
import LeanIn.Http.StdHandler

/-!
# `dispatchBench` — what the `Std`-shaped layer adds to a request

Drives one request head through the work each handler shape does at dispatch, in memory, once per iteration —
no sockets, no timers, no body — so the native `StreamHandler` path and the `StdHandler` layer are compared on
the work that differs and nothing else.

- **native**: parse the head with LeanIn's machine and build the `H1.ResponseHead` the writer encodes.
- **std**: the same parse, then `StdHandler.headToStock` (method, `RequestTarget.parse?`, the validated `Headers`
  map), the `Request` with its `RemoteAddr` extension, a stock `Response`, its conversion back with
  `StdHandler.responseHead`, and the `Date` header from the per-second cache.
- **head**: the std arm stopped after `headToStock`, so the head conversion and the rest are told apart.

Both arms run on two requests: `bench/load.mjs`'s (two headers) and a browser-shaped one (ten headers), because
the header map is the cost that grows with the request. `main` takes the iteration count (default 100000) and
prints ns/request per arm, alternating arms twice so a drift between runs is visible rather than averaged away.

Build the exe (`nix develop -c lake build dispatchBench`) and run it; `lean --run` would interpret the loops.
For instructions rather than nanoseconds, run it under `callgrind` with a small count.
-/

open LeanIn
open LeanIn.Http

def loadReq := "GET /bench HTTP/1.1\r\nHost: x\r\nConnection: keep-alive\r\n\r\n".toUTF8

def browserReq :=
  ("GET /todos/42/edit?filter=active&sort=asc HTTP/1.1\r\n" ++
   "Host: localhost:8080\r\n" ++
   "User-Agent: Mozilla/5.0 (X11; Linux aarch64; rv:131.0) Gecko/20100101 Firefox/131.0\r\n" ++
   "Accept: text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8\r\n" ++
   "Accept-Language: en-GB,en;q=0.5\r\n" ++
   "Accept-Encoding: gzip, deflate, br, zstd\r\n" ++
   "Referer: http://localhost:8080/todos\r\n" ++
   "Cookie: session=4f2a9c1e7b3d8e6f0a5c2b9d1e4f7a3c; flash=\r\n" ++
   "Connection: keep-alive\r\n" ++
   "Upgrade-Insecure-Requests: 1\r\n" ++
   "Sec-Fetch-Dest: document\r\n\r\n").toUTF8

/-- Parse a head with LeanIn's machine, as the streaming pump does. -/
def parse (req : ByteArray) : Option H1.Head := Id.run do
  let mut m : H1.Machine := { buffered := false }
  m := H1.Machine.feed m req
  for _ in [0:4] do
    let (m', step) := H1.Machine.step m
    m := m'
    for e in step.events do
      match e with
      | .endHeaders h => return some h
      | _ => pure ()
    if m.halted then break
  return none

def body : ByteArray := "hello from leanin\n".toUTF8

/-- The native arm: the head, and the response head the writer would encode. -/
def nativeOnce (req : ByteArray) : IO Nat := do
  let some head := parse req | return 0
  let rh : H1.ResponseHead :=
    { status := 200, reason := "OK", headers := #[("Content-Length", toString body.size)] }
  return head.headers.size + rh.headers.size

/-- The std arm's head conversion alone: the parse and `headToStock`, so the rest of the std arm is the
difference. -/
def headOnce (req : ByteArray) : IO Nat := do
  let some head := parse req | return 0
  let .ok line := StdHandler.headToStock head | return 0
  return line.headers.size

/-- The std arm: the same, through the stock request and response types. -/
def stdOnce (req : ByteArray) : IO Nat := do
  let some head := parse req | return 0
  let .ok line := StdHandler.headToStock head | return 0
  let extensions := Std.Http.Extensions.empty.insert (Std.Http.Server.RemoteAddr.mk (Runtime.loopback 40000))
  let request : Std.Http.Request Unit := { line, body := (), extensions }
  let headers := Std.Http.Headers.empty.insert Std.Http.Header.Name.contentLength
    (Std.Http.Header.Value.ofString! (toString body.size))
  let response : Std.Http.Response ResponseBody := { line := { status := .ok, headers }, body := .bytes body }
  let rh := StdHandler.responseHead response.line
  let d ← StdHandler.currentDate
  let rh := { rh with headers := rh.headers.push ("Date", d) }
  return request.line.headers.size + rh.headers.size

def bench (label : String) (n : Nat) (f : IO Nat) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let mut acc := 0
  for _ in [0:n] do acc := acc + (← f)
  let t1 ← IO.monoNanosNow
  IO.println s!"{label}: {(t1 - t0) / n} ns/request  (checksum={acc})"

public def main (args : List String) : IO Unit := do
  let n := (args.head?.bind (·.toNat?)).getD 100000
  for (name, req) in [("load.mjs", loadReq), ("browser ", browserReq)] do
    for _ in [0:2] do
      bench s!"{name} native" n (nativeOnce req)
      bench s!"{name} head  " n (headOnce req)
      bench s!"{name} std   " n (stdOnce req)
