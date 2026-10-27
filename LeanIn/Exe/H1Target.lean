module

import LeanIn.Http.H1

/-- `lake exe h1Target` checks the decoded path/query views on a hand-built head. -/
public def main : IO UInt32 := do
  let raw := "/a%20b?x=1+y&z=%2F".toUTF8
  let h : LeanIn.Http.H1.Head :=
    { buf := raw, target := { start := 0, stop := raw.size } }
  let ok := h.path? == some "/a b" && h.query? == some "x=1 y&z=/"
  let path := (h.path?).getD "<none>"
  let query := (h.query?).getD "<none>"
  let badRaw := "/bad%2".toUTF8
  let bad : LeanIn.Http.H1.Head :=
    { buf := badRaw, target := { start := 0, stop := badRaw.size } }
  let noQuery := (h.query? != none) && bad.path? == none
  IO.println s!"h1Target|path={path}|query={query}|ok={ok && noQuery}"
  return if ok then 0 else 1
