module

public import LeanIn
public import LeanIn.Runtime.Net
public import LeanIn.Runtime.VM
public import LeanIn.Async
public import LeanIn.Test.Machines

public section
open LeanIn

/-!
# `async` exercise harness

Small machines that compile the shapes the connection driver relies on — a suspension per iteration, loops and
their carried fields, `break`/`continue`, a close that ends the path — plus the two hand-written echo baselines
they are measured against (`cpsEcho` through the `Join`-cell delivery, `vmEcho` through the interpreted `VM`).
Run with `lake exe defuncEcho [port] [mode]`: `async`, `loop`, `for`, `brk`, `cont`, `forCont`, `vm`,
`parent`, `parentT` (composition with thread-id records, for SC23), `call`, `spawn` (SC25), `select`
(SC26), default `cps`.
-/

async def amEcho (c : LeanIn.Runtime.Conn) : Unit := do
  let req := await (LeanIn.Runtime.Io.recvRaw c 65536)
  await (LeanIn.Runtime.Io.sendAllRaw c #[req])
  recurse

-- Composition: a callable child (reads one request, echoes it, and answers its `onDone` with the bytes) and
-- a parent that awaits it twice per exchange — a machine awaiting a machine, with the parent's continuation
-- as the child's `onDone`, no cell.
async def amChunk (c : LeanIn.Runtime.Conn) : ByteArray := do
  let bs := await (LeanIn.Runtime.Io.recvRaw c 65536)
  await (LeanIn.Runtime.Io.sendAllRaw c #[bs])
  return bs

async def amParent (c : LeanIn.Runtime.Conn) : Unit := do
  let first : ByteArray := await (amChunk.run c)
  let second : ByteArray := await (amChunk.run c)
  await (LeanIn.Runtime.Io.sendAllRaw c #[first, second])
  recurse

-- The tid-recording pair for SC23: the child reports the thread its terminal step runs on, the parent reports
-- the thread each call resumes it on — the resume thread being the child's own completion thread (a raw
-- resume, no carrier hop), never the accept loop's.
async def amChunkT (c : LeanIn.Runtime.Conn) : ByteArray := do
  let bs := await (LeanIn.Runtime.Io.recvRaw c 65536)
  await (LeanIn.Runtime.Io.sendAllRaw c #[bs])
  (do let tid ← IO.getTID; IO.println s!"sc23|childStepTid={tid}"; (← IO.getStdout).flush)
  return bs

async def amParentT (c : LeanIn.Runtime.Conn) : Unit := do
  let first : ByteArray := await (amChunkT.run c)
  (do let tid ← IO.getTID; IO.println s!"sc23|resumeTid={tid}"; (← IO.getStdout).flush)
  let second : ByteArray := await (amChunkT.run c)
  (do let tid ← IO.getTID; IO.println s!"sc23|resumeTid={tid}"; (← IO.getStdout).flush)
  await (LeanIn.Runtime.Io.sendAllRaw c #[first, second])
  recurse

-- A child that only writes and returns, and a caller that awaits exactly one call per request — the
-- machine-call cost isolated against `amEcho` (the same loop with the write inline) and `vmEcho` (the
-- interpreted `VM`).
async def amWrite (c : LeanIn.Runtime.Conn) (bs : ByteArray) : ByteArray := do
  await (LeanIn.Runtime.Io.sendAllRaw c #[bs])
  return bs

async def amCall (c : LeanIn.Runtime.Conn) : Unit := do
  let bs := await (LeanIn.Runtime.Io.recvRaw c 65536)
  let _r : ByteArray := await (amWrite.run c bs)
  recurse

-- A loop as a state machine: send `msg0..msg2` (each an `await`), then close — the loop counter `i` is the
-- loop state's field, threaded across iterations. Exercises `while` in `async`.
async def amLoop (c : LeanIn.Runtime.Conn) : Unit := do
  let i : Nat := 0
  while i < 3 do
    await (LeanIn.Runtime.Io.sendAllRaw c #[s!"msg{i}\n".toUTF8])
    let i := i + 1
  await (LeanIn.Runtime.Io.closeRaw c)

-- `for` over an array: send each element (an await per element), then close.
async def amFor (c : LeanIn.Runtime.Conn) : Unit := do
  for x in (#[s!"a\n".toUTF8, s!"b\n".toUTF8, s!"c\n".toUTF8] : Array ByteArray) do
    await (LeanIn.Runtime.Io.sendAllRaw c #[x])
  await (LeanIn.Runtime.Io.closeRaw c)

-- `while` with `break`: send 0, 1, then break out and close.
async def amBreak (c : LeanIn.Runtime.Conn) : Unit := do
  let i : Nat := 0
  while i < 10 do
    if i == 2 then break
    await (LeanIn.Runtime.Io.sendAllRaw c #[s!"{i}\n".toUTF8])
    let i := i + 1
  await (LeanIn.Runtime.Io.closeRaw c)

-- `for` with `continue`: send a, c, skipping b by `continue` — the increment is owed on the skipped
-- iteration too, or c is never reached.
async def amForCont (c : LeanIn.Runtime.Conn) : Unit := do
  for x in (#[s!"a\n".toUTF8, s!"b\n".toUTF8, s!"c\n".toUTF8] : Array ByteArray) do
    if x == s!"b\n".toUTF8 then continue
    await (LeanIn.Runtime.Io.sendAllRaw c #[x])
  await (LeanIn.Runtime.Io.closeRaw c)

-- `while` with `continue`: send the odd numbers 1,3,5, skipping even by `continue`.
async def amContinue (c : LeanIn.Runtime.Conn) : Unit := do
  let i : Nat := 0
  while i < 5 do
    let i := i + 1
    if i % 2 == 0 then continue
    await (LeanIn.Runtime.Io.sendAllRaw c #[s!"{i}\n".toUTF8])
  await (LeanIn.Runtime.Io.closeRaw c)

/-- CPS echo: read, write back, recurse — every step through the `Join`-cell delivery (park, `Item`, carrier). -/
partial def cpsEcho (hooks : Runtime.Hooks) (c : Runtime.Conn) : Task.EAsync IO.Error Unit := do
  try
    match ← Runtime.Conn.recv c hooks with
    | none    => Runtime.Conn.shutdown c hooks
    | some bs => Runtime.Conn.send c hooks bs; cpsEcho hooks c
  catch _ => pure ()

/-- VM echo: the *same* logic, written in the defunctionalizing `VM` monad with ordinary `do`. -/
partial def vmEcho (c : Runtime.Conn) : Runtime.VM Unit := do
  match ← Runtime.VM.recv c with
  | some bs => Runtime.VM.send c bs; vmEcho c
  | none    => Runtime.VM.close c

/-- Start a long-lived machine without waiting for a terminal it may never reach. -/
def detached : LeanIn.Async.Completion Unit :=
  { done := fun _ => pure (), fail := fun e => IO.eprintln s!"defuncEcho: {e}" }

partial def acceptLoop (e : LeanIn.Sched.Executor LeanIn.Task.Item 256)
    (hooks : Runtime.Hooks) (l : Runtime.Listener) (mode : String) :
    Task.EAsync IO.Error Unit := do
  let c ← Runtime.Listener.accept l hooks
  if mode == "vm" then
    monadLift (Runtime.VM.run (vmEcho c))
  else if mode == "parent" then
    monadLift (amParent.run c detached)
  else if mode == "parentT" then
    let tid ← monadLift (IO.getTID : IO UInt64)
    monadLift (IO.println s!"sc23|acceptTid={tid}")
    monadLift (IO.getStdout >>= fun s => s.flush : IO Unit)
    monadLift (amParentT.run c detached)
  else if mode == "call" then
    monadLift (amCall.run c detached)
  else if mode == "async" then
    monadLift (amEcho.run c detached)
  else if mode == "loop" then
    monadLift (amLoop.run c detached)
  else if mode == "for" then
    monadLift (amFor.run c detached)
  else if mode == "brk" then
    monadLift (amBreak.run c detached)
  else if mode == "cont" then
    monadLift (amContinue.run c detached)
  else if mode == "forCont" then
    monadLift (amForCont.run c detached)
  else if mode == "spawn" then
    monadLift (amSpawn.run c (Runtime.sharedPush e) "AAA".toUTF8 "BBB".toUTF8 detached)
  else if mode == "select" then
    monadLift (amSelect.run c detached)
  else
    let _ ← Task.MonadAsync.spawn (cpsEcho hooks c)
  acceptLoop e hooks l mode

def main (args : List String) : IO UInt32 := do
  let port := (args.head?.bind (·.toNat?)).getD 8080
  let mode := args.getD 1 "cps"
  let hooks ← Runtime.Hooks.new
  let l ← Runtime.Listener.bind (Runtime.loopback port.toUInt16)
  let e ← Sched.Executor.new LeanIn.Task.Item 256 1
  if mode == "parentT" then
    -- The single-carrier entry: one thread is the accept loop, the connection's effects, and the resume —
    -- and the loop's own pump. The dedicated task's tid is the detector's control that distinct threads
    -- read distinct tids in this process.
    IO.println s!"sc23|mainTid={← IO.getTID}"
    let dt ← IO.asTask IO.getTID Task.Priority.dedicated
    IO.println s!"sc23|dedicatedTid={(← IO.wait dt).toOption.getD 0}"
    (← IO.getStdout).flush
    let _ : Except IO.Error Unit ← Runtime.run e (acceptLoop e hooks l "parentT")
  else
    let _ : Except IO.Error Unit ← Runtime.run e (acceptLoop e hooks l mode)
  return 0

end
