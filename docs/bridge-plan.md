# The runtime bridge: the decision, the corrections, and the programme

`LeanIn/Theory/Bridge.lean` states seven axioms — A1–A5 and A7 — as the whole of the trusted connection
between the model in `LeanIn/Theory/World.lean` and the running `BaseIO` operations. This document
records what those statements can and cannot carry, the single decision the rest follows from, the
corrections that decision implies, and the larger undertaking that would replace them with a
machine-checked correspondence.

It is the second half of a pair. `LeanIn_Bridge_Axioms_Handoff.txt` at the repository root argues for
an execution contract, written from `Bridge.lean` alone — `World.lean` and the scheduler were not
available to it, which it says. Its direction is right. This document records which of its requirements
are already met, which are live defects in the axioms as they stand, and which are a larger
undertaking than a correction.

## What is already in place

As of `0ee1f5f`:

- **The acting thread.** `Runs t op w r w'` names the thread that executes `op`, so the axioms say what
  their comments always claimed: A1's owner is *the caller*, not "some `t` for every `t`".
- **A2's failure case.** `tryLock_spec` carries the standard's non-ownership precondition and concludes
  both that ownership is unchanged and that the caller is not the owner. Before, a world in which the
  caller already held the lock and `tryLock` returned `false` satisfied it — which is the case the
  standard leaves undefined, as the A2 control in `LeanIn/Test/Control.lean` says in as many words.
- **The wait cycle, as a path.** `wait_spec` concludes that the caller holds the lock again *and* has
  stopped being a waiter; `World.wait_cycle_reachable` exhibits the three-step path the call spans —
  park, resume, re-acquire — and `World.afterWait_releases` shows it cannot be one step, because the
  model's own `wait` step leaves the lock free. `World.reacquisition_is_anyone` records the control:
  any thread may take the freed lock, so the caller's re-acquisition is a scheduler decision the
  refinement must carry, not a model consequence.
- **At most one, and all.** `notifyOne_spec` bounds the loss at one entry; `notifyAll_spec` says every
  waiter present at the call is gone. They are no longer the same proposition, and the second now
  carries the clearing the shutdown path depends on.
- **No fairness, no progress.** A1 has no vocabulary for a pending request, and the property ladder
  keeps liveness (P2, P9) outside the base bridge.

## The decision everything else follows from

**What does `w'` in `Runs t op w r w'` denote?**

- **(a) The world on return**, including whatever other actors did while the call was in flight. This is
  the reading the file currently invites: A1's comment says the property is "stated as a property of the
  returned world". It is the honest reading for a call that takes time on a machine where other threads
  run — and it is what the handoff assumes when it says a later carrier may acquire before the call
  interval ends.
- **(b) The world after *this operation's* effect alone**, with other actors' steps in the interval as
  separate transitions or as stuttering. Then `w'` is one step of this operation, and a multi-step call
  such as `wait` needs a *path* rather than an endpoint — which the model now has.

Under (a), a postcondition may state only properties that other actors cannot change: *holding* a lock
cannot be taken away during the call, so A1, A2's success case and A4 are safe; *not holding* it can be
taken away, so A3 and the failure case of A2 are not. Under (b) both become correct as written, at the
cost of an explicit relation between the returned world and `w'`.

**Recommended: (b), with the interval made explicit.** State the operation's own effect over `w'`, and
state separately how the returned world relates to it — the handoff's "map harmless untracked effects to
stuttering", and its requirement that environment steps are attributed to the environment. That keeps
the event statements correct *and* keeps the ability to say what happened in between.

Everything in the next section is a consequence of this choice. It is worth making it once, in the file,
in a comment above `Runs`, rather than re-deriving it per axiom.

## The corrections

Each is small once the decision above is made. None of them requires the programme in the next section.

| # | what | where | the failure it prevents |
|---|---|---|---|
| C1 | Record the meaning of `w'` for the whole file | `Bridge.lean`, above `Runs` | C2–C5 are otherwise re-litigated per axiom |
| C2 | State `unlock`'s effect as a release, not as "the returned world is unowned" | `unlock_spec` | another carrier may acquire before the call returns |
| C3 | Scope A2's failure case to "no ownership change *by this operation*" | `tryLock_spec` | same; a concurrent acquisition changes the returned world |
| C4 | Record the clock sample, or relate successive ordered reads directly | `clock_spec`, `World` | two reads are related only to a clock that never moves, so no monotonicity — and no budget — is derivable. `Control.controlClock` tests a property the axiom does not state |
| C5 | Use a membership or episode form for `notifyOne`, not a cardinality bound | `notifyOne_spec` | two concurrent enrolments during the call interval break `length ≤ length + 1`, and cardinality says nothing about *which* episode left |
| C6 | Make the object correspondence a stable per-object map, and have every axiom re-establish it | `Bridge.lean`, `World` | No conclusion in the file mentions `IsLock`, so after any call you no longer know that `m` is the lock at `l`. **The axioms are not composable**: no multi-step refinement can be built from them today. This is why nothing downstream consumes them |
| C7 | Name the actors: a native carrier or waker thread, as against a green task | `World`, `Bridge` | `abbrev Tid := Nat` carries no meaning. Ownership of `Std.BaseMutex` and `Std.Condvar` is native-thread-level — `WakerSpike`'s `inboxPush` takes the same mutex from a pool worker — and no green task owns a mutex. The handoff's `CarrierId` is the right distinction |
| C8 | Model waiters as a set or as episodes, with the invariant stated | `World` | duplicates are representable and have already cost one defect: `afterSpurious` used `List.erase`, which removes only the first occurrence, so a doubly-enrolled thread that woke spuriously stayed a waiter |
| C9 | Say whether any claim depends on data read under the lock | `Bridge`, `docs/interface.md` | ownership fields do not establish visibility; the model tracks owners and waiters, not memory contents |

C6 is the one that matters most. It is not a cosmetic gap: it is the reason the axioms are currently
unusable, and it is the same point the handoff makes when it asks for a stable per-object map instead of
independent world-indexed claims.

## The programme, separated

The handoff proposes replacing endpoint assumptions with an execution contract: a defined runtime
history, a representation relation, an abstract event path, and a prefix-correspondence theorem. That is
a different order of work from the corrections above, and it is the hard part the plan already names —
`docs/proof-strategy.md` Gap A and T1/T6, with option (1) (correct pure bodies over `@[extern]`, argued
correspondence) as the near-term default and option (3) (a modelled semantics) as the research bet.

What it would buy: the argued correspondence discharged into a machine-checked one, and the TCB made
enumerable — the primitives, the compiler, the platform, each named.

What it costs: a semantics for the supported `BaseIO` fragment, which no one has; liveness still out of
reach (T2); and a set of new files (`Execution`, `Representation`, `BridgeLemmas`,
`SchedulerRefinement`, `BridgeControls`).

**It is a scope decision, not a patch.** Taking it would replace the milestone's approach rather than
correct it, so it belongs with the owner of the plan, not in a repair.

## What not to do

- **Do not patch C2–C5 before C1.** Each is a conclusion tweak whose correctness depends on what `w'`
  means; patched first, they will be re-litigated.
- **Do not adopt the handoff's architecture as a correction.** Its contract-level requirements are worth
  taking now; its programme is the T1/T6 work.
- **Do not describe the result as a proved native refinement.** The honest description is a
  machine-checked scheduler proof conditional on explicit runtime contracts — which is the handoff's own
  wording, and matches `docs/proof-strategy.md` §6.

## The evidence, and its limits

The findings above come from reading the seven axioms, `World.lean`, `Control.lean` and
`LeanIn_Bridge_Axioms_Handoff.txt`, together with the repairs already landed.

Two limits are worth stating plainly:

- **None of these defects is a provable inconsistency.** `Runs` is `opaque` with no introduction rules,
  so no Lean counterexample can be exhibited without an interpretation of `Runs` — which is itself part
  of the programme. These are *fidelity* failures: the axiom set forbids behaviours the machine permits,
  or fails to state properties the model relies on. They are detectable by reading, and the handoff's
  countermodel list is the right shape for turning each into a test at the native level.
- **The handoff was written without `World.lean`**, so it cannot see the model's own defects. Its C8
  requirement — "if waiter lists remain in `World`, prove `NoDup` and exact membership updates" — covers
  the class that produced one of them.

## Open questions

1. What `w'` denotes (the decision above), or an explicit delegation of it.
2. Whether the execution-contract programme enters scope now, later, or not at all.
3. Whether native actor and wait-episode identities belong in the model or only in the bridge.
4. Whether `LeanIn_Bridge_Axioms_Handoff.txt` belongs in the repository at its current path, under a
   name in the repository's style, or outside it.
