module

public import LeanIn
public import LeanIn.Async
public import LeanIn.Runtime.Net

public section

/-!
# Scenario machines for the time-as-effect controls

`amDelayed` and `amStall` are the compiled machines SC24 serves: one sleeps `d` on the injected clock between
read and answer (`sleepRaw`), the other races a read against the same stated instant (`recvTimeoutRaw`). Each
reports its close *submission* on `onDone` — the connection's closure is observed separately, by the client
reading to EOF — so a harness can hold the run until the machine's terminal step rather than its first
suspension.
-/

open LeanIn

-- Read a request, sleep `d` on the injected clock, answer, close, and report the close.
async def amDelayed (c : LeanIn.Runtime.Conn) (clock : LeanIn.Runtime.Clock)
    (d : Std.Time.Millisecond.Offset) : Unit := do
  let bs := await (LeanIn.Runtime.Io.recvRaw c 65536)
  await (LeanIn.Runtime.Io.sleepRaw clock.schedule d)
  await (LeanIn.Runtime.Io.sendAllRaw c #[bs])
  let closed := await (LeanIn.Runtime.Io.closeRaw c)
  if closed then return () else throw (IO.userError "amDelayed: the loop refused the close")

-- Race a read against the stated instant: answer an arrived request, close with nothing written on the
-- deadline or on end of stream, and report the close (the transport error is reported too).
async def amStall (c : LeanIn.Runtime.Conn) (clock : LeanIn.Runtime.Clock)
    (d : Std.Time.Millisecond.Offset) : Unit := do
  let rt := await (LeanIn.Runtime.Io.recvTimeoutRaw c clock.schedule d 65536)
  match rt with
  | none =>
    let closed := await (LeanIn.Runtime.Io.closeRaw c)
    if closed then return () else throw (IO.userError "amStall: the loop refused the close")
  | some (.ok (some bs)) =>
    await (LeanIn.Runtime.Io.sendAllRaw c #[bs])
    let closed := await (LeanIn.Runtime.Io.closeRaw c)
    if closed then return () else throw (IO.userError "amStall: the loop refused the close")
  | some (.ok none) =>
    let closed := await (LeanIn.Runtime.Io.closeRaw c)
    if closed then return () else throw (IO.userError "amStall: the loop refused the close")
  | some (.error e) =>
    let closed := await (LeanIn.Runtime.Io.closeRaw c)
    if closed then throw e else throw (IO.userError s!"{e}; and the loop refused the close")

-- A spawned child: deliver a threaded payload on its continuation and halt. The connection is carried
-- (the spawn surface takes one) but unused, so the child's only executor work is its boot.
async def amChunkOf (c : LeanIn.Runtime.Conn) (payload : ByteArray) : ByteArray := do
  return payload

-- Spawn two children — always the first carrying `b`, the second `a` — and join them in the order the
-- request byte names: `0` joins the first-spawned handle then the second, `1` the reverse. Identical spawns
-- with swapped join orders are what distinguishes a join-order collector from a completion-order one.
async def amSpawn (c : LeanIn.Runtime.Conn) (push : LeanIn.Task.Item → BaseIO Unit)
    (a : ByteArray) (b : ByteArray) : Unit := do
  let sel := await (LeanIn.Runtime.Io.recvRaw c 65536)
  let h0 : LeanIn.Runtime.RawCell (Except IO.Error ByteArray) := await (amChunkOf.spawn push c b)
  let h1 : LeanIn.Runtime.RawCell (Except IO.Error ByteArray) := await (amChunkOf.spawn push c a)
  if sel == "1".toUTF8 then
    let r1E : Except IO.Error ByteArray := await (LeanIn.Runtime.RawCell.await h1)
    let r1 : ByteArray := r1E.toOption.getD .empty
    let r0E : Except IO.Error ByteArray := await (LeanIn.Runtime.RawCell.await h0)
    let r0 : ByteArray := r0E.toOption.getD .empty
    let ok := await (LeanIn.Runtime.Io.sendAllRaw c #[r1, r0])
    let closed := await (LeanIn.Runtime.Io.closeRaw c)
    if closed then return () else throw (IO.userError "amSpawn: the loop refused the close")
  else
    let r0E : Except IO.Error ByteArray := await (LeanIn.Runtime.RawCell.await h0)
    let r0 : ByteArray := r0E.toOption.getD .empty
    let r1E : Except IO.Error ByteArray := await (LeanIn.Runtime.RawCell.await h1)
    let r1 : ByteArray := r1E.toOption.getD .empty
    let ok := await (LeanIn.Runtime.Io.sendAllRaw c #[r0, r1])
    let closed := await (LeanIn.Runtime.Io.closeRaw c)
    if closed then return () else throw (IO.userError "amSpawn: the loop refused the close")

-- Select over two cells, clause chosen by the first request byte.
-- `A`: `h1` resolves before the select and `h0` after it — first-resolved wins (index 1), and the later
-- resolution is ignored.
-- `B`: both resolve before the select — registration order is the tie rule (index 0).
-- The answer is `A<i>`/`B<i>` carrying the winning index.
async def amSelect (c : LeanIn.Runtime.Conn) : Unit := do
  let sel := await (LeanIn.Runtime.Io.recvRaw c 65536)
  let h0 : LeanIn.Runtime.RawCell ByteArray := await (LeanIn.Runtime.RawCell.new)
  let h1 : LeanIn.Runtime.RawCell ByteArray := await (LeanIn.Runtime.RawCell.new)
  if sel == "A".toUTF8 then
    let u1 : Unit := await (LeanIn.Runtime.RawCell.resolve h1 "one".toUTF8)
    let pair : Nat × ByteArray := await (LeanIn.Runtime.selectRaw h0 h1)
    let w : Nat := pair.1
    let got : ByteArray := pair.2
    let u0 : Unit := await (LeanIn.Runtime.RawCell.resolve h0 "zero".toUTF8)
    let ok := await (LeanIn.Runtime.Io.sendAllRaw c #[s!"A{w}".toUTF8 ++ got])
    let closed := await (LeanIn.Runtime.Io.closeRaw c)
    if closed then return () else throw (IO.userError "amSelect: the loop refused the close")
  else
    let u0 : Unit := await (LeanIn.Runtime.RawCell.resolve h0 "zero".toUTF8)
    let u1 : Unit := await (LeanIn.Runtime.RawCell.resolve h1 "one".toUTF8)
    let pair : Nat × ByteArray := await (LeanIn.Runtime.selectRaw h0 h1)
    let w : Nat := pair.1
    let got : ByteArray := pair.2
    let ok := await (LeanIn.Runtime.Io.sendAllRaw c #[s!"B{w}".toUTF8 ++ got])
    let closed := await (LeanIn.Runtime.Io.closeRaw c)
    if closed then return () else throw (IO.userError "amSelect: the loop refused the close")

end
