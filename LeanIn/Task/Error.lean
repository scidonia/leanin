import LeanIn.Task.Basic

/-!
# Failures as values

The absence this file fills: our `Async` had no error channel, so a leaf that failed could not tell its awaiter —
`Leaf.lean`'s panicking conversions were what stood in its place, which is right for a client that has decided a
failure is a defect and wrong for a server, where a client going away mid-request is an ordinary event.

The shape is the shipped one (`Std.Async`'s `EAsync`, and `EIO` before it): the error rides in the *value*, so
`EAsync ε α` is `Async (Except ε α)`, `bind` short-circuits on `error`, and the handle an awaiter receives is a
handle on the failing computation. Nothing in the task layer changes — this is a layer over it, which is why it
needs no new scheduling and no new resolution law.
-/

namespace LeanIn.Task

/-- A computation whose failure is a value rather than a panic. -/
abbrev EAsync (ε : Type) (α : Type) := Async (Except ε α)

namespace EAsync

/-- A computation that cannot fail, lifted. -/
def ofAsync (a : Async α) : EAsync ε α :=
  ⟨fun k ctx => a.step (fun v => k (.ok v)) ctx⟩

/-- Fail now. -/
def fail (e : ε) : EAsync ε α :=
  ⟨fun k _ => k (.error e)⟩

/-- Sequencing short-circuits on `error`; nothing runs after a failure. -/
instance : Monad (EAsync ε) where
  pure v := ⟨fun k _ => k (.ok v)⟩
  bind a f := ⟨fun k ctx => a.step (fun r => match r with
    | .ok v    => (f v).step k ctx
    | .error e => k (.error e)) ctx⟩

/-- The channel itself: `throw` fails a computation, `tryCatch` handles one. -/
instance : MonadExcept ε (EAsync ε) where
  throw e := fail e
  tryCatch a h := ⟨fun k ctx => a.step (fun r => match r with
    | .ok v    => k (.ok v)
    | .error e => (h e).step k ctx) ctx⟩

/-- An `IO` action in this layer: its error is the failure. -/
instance : MonadLift IO (EAsync IO.Error) where
  monadLift act := ofAsync (Async.ofIO act)

/-- A `BaseIO` action in this layer, which is what the runtime's primitives are — `IO.getTID` among them.
Separate from the `IO` instance because instance search does not chain lifts. -/
instance : MonadLift BaseIO (EAsync IO.Error) where
  monadLift act := ofAsync (Async.ofIO (liftM act))

/-- Awaiting a handle on a failing computation yields its `Except`, so the error travels with the value. -/
instance : MonadAwait (EAsync ε) where
  Handle := fun α => Task (Except ε α)
  await h := Async.await h

/-- Starting a computation cannot itself fail, so the handle arrives as `ok`. -/
instance : MonadAsync (EAsync ε) where
  spawn a := ⟨fun k ctx => (Async.spawn a).step (fun h => k (.ok h)) ctx⟩

end EAsync

end LeanIn.Task
