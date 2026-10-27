module

public import LeanIn.Runtime.Basic

public section

/-!
# The executor's narrowing, verified across modules

`Sched.Executor`'s constructor and every field are private to `LeanIn.Sched`, so the carrier-side surface is
reachable only through the operations this library declares — the same mechanism `Runtime.Handle` uses. Each
route a caller could otherwise take is refused here, with an affirmative control beside it, so a build is a
reading about checks that can fail. The control is enforced by the compiler: `#check_failure` reports an error
if its term *elaborates*, so a field or constructor that became public turns this file into a build failure.

**What this does not reach, stated rather than implied**: the *admission* to a queue. The marker-requiring
pushes (`Executor.pushInject`/`spawnLocal`/`submitLocal`, which take a `Sendable`) live in
`LeanIn/Task/Send.lean`, and the raw transactions they wrap (`pushInjectRaw`/`spawnLocalRaw`/`submitLocalRaw`)
are public because `Sendable` is declared *above* `Sched.Executor` in the import graph (`Executor` ←
`Task.Basic` ← `Task.Send`): no module the executor can see can both mint a `Sendable` (which needs `Item`) and
consume it (which needs the executor's internals), so a private raw push is unreachable by the very module that
would mark it. The runtime never calls a raw push, which is an audit fact, not a compiler one.
-/

namespace LeanIn.Test

-- The affirmative control: the public operations are reachable.
#check (fun (e : LeanIn.Sched.Executor Nat 256) => e.workerCount)
#check (fun (e : LeanIn.Sched.Executor Nat 256) => e.isStopping)

-- Route 1: field access.
#check_failure (fun (e : LeanIn.Sched.Executor Nat 256) => e.workers)

-- Route 2: the constructor constant.
#check_failure LeanIn.Sched.Executor.mk

-- Route 3: pattern matching on the structure.
#check_failure (fun (e : LeanIn.Sched.Executor Nat 256) => match e with
  | ⟨a, b, c, d, f, g, h, i⟩ => a)

-- Route 4: structure notation.
#check_failure (({ workers := (Array.empty : Array (Std.Mutex (LeanIn.Sched.Pool Nat 256))) }
  : LeanIn.Sched.Executor Nat 256))

-- Route 5: structure-update notation (the shape `Runtime` used before the narrowing).
#check_failure (fun (e : LeanIn.Sched.Executor Nat 256) => { e with metered := true })

end LeanIn.Test

end
