module

import LeanIn.Http.H1
import Std.Http.Protocol.H1

/-!
# `h1bench` — the head-parse microbenchmark

Drives one HTTP/1.1 request through `Std.Http.Protocol.H1`'s machine and through `LeanIn.Http.H1`'s, in memory,
once per iteration — no sockets, no timers, no response — so the two parsers are compared on the work each does
for the same bytes, and nothing else. `main` takes the iteration count (default 100000) and prints ns/parse per
arm, alternating arms twice so a run-to-run drift is visible rather than averaged away.

`lean --run` would interpret these loops and favour the arm that interprets better; build the exe
(`nix develop -c lake build h1bench`) and run it, and pair it with `callgrind` for instructions rather than
nanoseconds — see §3.6 of `docs/PERFORMANCE.md` for the recorded figures and how to read them.
-/

open LeanIn.Http

def req := "GET /bench HTTP/1.1\r\nHost: x\r\nConnection: keep-alive\r\n\r\n".toUTF8

/-- Drive Std's machine once over `req`, return 1 if an endHeaders was seen. -/
def stdOnce : IO Nat := do
  let mut m : Std.Http.Protocol.H1.Machine .receiving := { config := {} }
  m := m.feed req
  let mut seen := 0
  for _ in [0:4] do
    let (m', step) := m.step
    m := m'
    if step.events.any (fun e => match e with | .endHeaders _ => true | _ => false) then
      seen := seen + 1
      break
    if m.halted then break
  return seen

/-- Drive ours once over `req`. -/
def ourOnce : IO Nat := do
  let mut m : H1.Machine := {}
  m := H1.Machine.feed m req
  let mut seen := 0
  for _ in [0:4] do
    let (m', step) := H1.Machine.step m
    m := m'
    if step.events.any (fun e => match e with | .endHeaders _ => true | _ => false) then
      seen := seen + 1
      break
    if m.halted then break
  return seen

def bench (label : String) (n : Nat) (f : IO Nat) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let mut acc := 0
  for _ in [0:n] do acc := acc + (← f)
  let t1 ← IO.monoNanosNow
  IO.println s!"{label}: {(t1 - t0) / n} ns/parse  (parsed={acc})"

public def main (args : List String) : IO Unit := do
  let n := (args.head?.bind (·.toNat?)).getD 100000
  bench "std " n stdOnce
  bench "ours" n ourOnce
  bench "std " n stdOnce
  bench "ours" n ourOnce
