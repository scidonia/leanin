module

import LeanIn

open LeanIn

def catchScope : IO Bool := do
  let seen ← IO.mkRef (0 : Nat)
  let comp : Runtime.VM Unit := do
    try
      pure ()
    catch _ => seen.modify (· + 1)
    throw (.userError "after")
  try Runtime.VM.run comp catch _ => pure ()
  return (← seen.get) == 0

def finalizerCase (body : Runtime.VM Unit) : IO Nat := do
  let seen ← IO.mkRef (0 : Nat)
  let comp : Runtime.VM Unit := do
    let _ ← MonadFinally.tryFinally' body (fun _ => do seen.modify (· + 1))
    pure ()
  try Runtime.VM.run comp catch _ => pure ()
  return (← seen.get)

def finalizerFailure : IO Nat := do
  let seen ← IO.mkRef (0 : Nat)
  let comp : Runtime.VM Unit := do
    let _ ← MonadFinally.tryFinally' (pure () : Runtime.VM Unit)
      (fun _ => (do seen.modify (· + 1); throw (.userError "fin") : Runtime.VM Unit))
    pure ()
  try Runtime.VM.run comp catch _ => pure ()
  return (← seen.get)

public def main : IO UInt32 := do
  let scope ← catchScope
  let pureCount ← finalizerCase (.pure ())
  let throwCount ← finalizerCase (.throwE (.userError "boom"))
  let abortCount ← finalizerCase (.abortE (.userError "abort"))
  let failCount ← finalizerFailure
  let ok := scope && pureCount == 1 && throwCount == 1 && abortCount == 1 && failCount == 1
  IO.println s!"vmScope|scope={scope}|pure={pureCount}|throw={throwCount}|abort={abortCount}|finalizerFailure={failCount}|ok={ok}"
  return if ok then 0 else 1
