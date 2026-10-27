module

import LeanIn
import LeanIn.Async
open LeanIn

-- A hand-written private `run` that ends in a completion is not a compiled machine: resolving private names
-- must not bypass the provenance tag, so this must be REJECTED for its missing tag, not as unknown.
def Fake.run (c : LeanIn.Runtime.Conn) (k : LeanIn.Async.Completion ByteArray) : IO Unit :=
  k.done ByteArray.empty

async def caller (c : LeanIn.Runtime.Conn) : ByteArray := do
  let bs : ByteArray := await (Fake.run c)
  return bs
