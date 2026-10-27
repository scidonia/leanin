module

public import LeanIn.Task.Send

public section

/-!
# The carrier boundary's control: what may cross it

`LeanIn/Task/Send.lean`'s marker is enforced by the compiler, not by a scenario, so its control is an
elaboration check rather than a runtime observation: a `Sendable` is built exactly where the library builds
one, and a module that is not `LeanIn.Task` cannot build one at all. The negative check is the affirmative
control's counterpart in the same file — one check that a `Sendable` exists, one that constructing one here
does not — so a green build is a reading about a check that can also fail, not a check that silently passes.

The property this fixes is narrow and stated: the marker narrows what crosses a *carrier boundary*, and a
caller's captured environment is not a type this library names (`LeanIn/Task/Send.lean` states the
convention half). What is checked here is the half the mechanism does enforce.
-/

namespace LeanIn.Test

-- The affirmative control: a `Sendable Item` exists where the library makes one.
#check (LeanIn.Task.Item.sendable default)

-- The negative control: `Sendable`'s constructor is private to `LeanIn.Task`, so a `Sendable` cannot be built
-- from this module — a value the library did not build cannot be marked for the carrier boundary.
#check_failure (LeanIn.Sendable.mk (1 : Nat))

end LeanIn.Test

end
