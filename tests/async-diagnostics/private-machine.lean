module

import LeanIn
import LeanIn.Async
open LeanIn

-- Machines declared outside a `public section` are private in a module. A machine calling one, and a
-- machine spawning one, must still find the private `run` and `spawn` the generator declared beside it — this
-- must ELABORATE.

/-- A private child, with a doc comment: the generator attaches it to the declared (private) name. -/
async def child (c : LeanIn.Runtime.Conn) (payload : ByteArray) : ByteArray := do
  return payload

async def caller (c : LeanIn.Runtime.Conn) : ByteArray := do
  let bs : ByteArray := await (child.run c "x".toUTF8)
  return bs

async def spawner (c : LeanIn.Runtime.Conn) (push : LeanIn.Task.Item → BaseIO Unit) : Unit := do
  let h : LeanIn.Runtime.RawCell (Except IO.Error ByteArray) := await (child.spawn push c "y".toUTF8)
  return ()
