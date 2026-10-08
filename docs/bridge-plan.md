# The runtime bridge: the decision, the corrections, and the programme

`LeanIn/Theory/Bridge.lean` states seven axioms — A1–A5 and A7 — as the whole of the trusted connection
between the model in `LeanIn/Theory/World.lean` and the running `BaseIO` operations. This document
records what those statements can and cannot carry, the single decision the rest follows from, the
corrections that decision implies, and the larger undertaking that would replace them with a
machine-checked correspondence.

**Status.** C1, C4, C7 and the method rule C10 are implemented and verified. C6 is half done — its
composability half holds, its no-aliasing half did not, and C11 is what corrects that. C12 corrects an
incompleteness in C4. The table records each, and what became of the rest.

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

**Chosen: (b).** The operation's own effect is stated over `w'`; other threads acting during the call
are separate transitions, and `Step` — a relation over single actions — is where they live. The
convention is stated once above `Runs` rather than re-derived per axiom.

**Three of the nine items in the next section retire with that choice**, and it is worth being explicit
about it, because they were conditions on the reading we rejected rather than defects of the file:

- **C2 and C3 need no statement change.** Under (b) a release *is* `owner = none` in the operation's own
  post-state, and a failed `tryLock` *is* "no ownership change by this operation". They were corrections
  to (a), and the reason (a) was rejected is precisely that the returned world cannot carry them.
- **C5 folds into C8.** Its soundness objection — concurrent enrolment breaking a cardinality bound —
  was an interval objection. What survives is an *adequacy* question about which episode leaves, which
  is the episode representation C8 asks for.

The remaining items are the work, and they are independent of each other except where noted.

## The corrections

Each is small once the decision above is made. None of them requires the programme in the next section.

| # | what | where | status |
|---|---|---|---|
| **C1** | State what `w'` denotes, once, for the whole file | `Bridge.lean`, above `Runs` | **done** — (b), with the reason (a) was rejected recorded there |
| **C4** | Record the clock sample, so successive reads are comparable | `clock_spec`, `World.lastSample` | **done** — three conjuncts: model time does not move, the reading is recorded, and it is never behind the previous sample |
| **C6** | Carry the object correspondence outside the world | `Rep`, `IsLock`, `IsCondvar` | **half done, and the other half was a defect — see C11.** Composability is done and `calls_compose` is its guard: three axioms on the same objects, which did not compile before. The *no aliasing* half was claimed and not delivered |
| **C7** | Say what an actor is | `World.lean`, `abbrev Tid` | **done** — a native thread, carrier or waker, never a green task |
| **C10** | Declare assumption-predicates with `axiom`, never `opaque` | — | **done, and insufficient on its own — see C11.** Found by testing the audit rather than reading it. Visibility is not content: an `axiom` predicate is named by `#print axioms` and can still say nothing |
| **C11** | State an assumption *and enforce it where it is needed*: `Rep.NonAliasing` is a local, pairwise condition | `Rep`, `distinct_mutexes_are_distinct_locks` | **done** — the guard is a theorem that relates two mutexes, so the hypothesis is required and consumed rather than suppressed |
| **C12** | Non-clock operations preserve the clock state | `World.SameClock`, six axioms | **done** — `readings_monotone_across_a_call` is the guard: it did not follow before |
| **C13** | Contract the two creation primitives | `newMutex_spec`, `newCondvar_spec` | **done** — two of the eight native operations had no contract at all. The *state* a fresh object is in is stated; *identity* is not, and cannot be without liveness and allocation identities in the model, which is why `Rep.NonAliasing` stays a hypothesis rather than a consequence |
| C2, C3, C5 | — | — | **retired or folded** with the choice of (b); see above |
| **C8** | Model waiters as a set or as episodes, with the invariant stated | `World.Condvar` | **open** — the largest remaining item: it changes the four waiter transitions and every A4 theorem |
| **C9** | Say whether any claim depends on data read under the lock | `Bridge`, `docs/interface.md` | **open** — documentation, no code |

C6 was the one that mattered most, and it was the reason the axioms were unusable rather than merely
incomplete: no conclusion mentioned `IsLock`, so after a first call the representation was lost and no
second call on that object could be stated. `calls_compose` is a regression guard as much as a
demonstration — make the representation world-indexed again and it stops compiling.

### C10 — an assumption stated as an `opaque` predicate is invisible to the audit

Found by testing rather than reading, and it matters more than its size suggests. `opaque` gives a
declaration a hidden *value*, so it is not an axiom and `#print axioms` never names it:

    theorem uses_rep_wf {r : Rep} (h : Rep.WF r) : Rep.WF r := h
    #print axioms uses_rep_wf          -- "does not depend on any axioms"
    #print axioms uses_a_bridge_axiom  -- "depends on axioms: [lock_spec]"

So the standing condition on the representation, first written as an `opaque`, would have been an
unstated assumption — invisible to the one check that exists to enumerate the trusted base, and in
direct conflict with the standard in `PLAN.md` §8 that nothing in the trusted base is unstated. The
rule is recorded in `AGENTS.md`, and it applies to every assumption-predicate rather than to this one.
C11 is the rest of it: stating an assumption is not the same as enforcing it.

### Two defects the first version carried

**The representation condition was named, not stated.** It was declared `axiom Rep.WF (r : Rep) : Prop`
— an *uninterpreted* proposition. The comment said distinct live objects keep distinct indices; the
declaration said nothing, so Lean could derive nothing from it, a constant `lockOf` sending every mutex
to one index satisfied it, and two independent runtime mutexes could alias a single model lock while
successive `lock_spec` applications overwrote one model owner. That is the failure this document exists
to describe, inside the change that describes it: *a comment promising more than the declaration
carries.* Making it an `axiom` (C10) had made it auditable without making it true, which hid the gap
rather than exposing it.

Replacing it with content was not enough either. The second version defined `Rep.Injective` — global
injectivity over every `Std.BaseMutex` — which is stronger than the runtime guarantees, since the
allocator may reuse a freed object's address and the guarantee holds only for objects that are
simultaneously live. Worse, it was **not enforced**: it was attached to a theorem combining one mutex
with one condvar, whose indices index *different* maps of `World`, so a coincidence between them denotes
nothing and neither half of the condition was used. The unused hypothesis showed up as a suppressed
linter warning, which is the tell that it guarded nothing.

What stands now is local and consumed: `Rep.NonAliasing r m₁ m₂` says two *mutexes* occupy different
model locks; `distinct_mutexes_are_distinct_locks` is a theorem relating two mutexes, so the hypothesis
is required there and used rather than suppressed; and the operation axioms do not carry it, because no
single operation relates two runtime objects. A use that relates two of them supplies it, or holds two
runtime mutexes whose shared model lock reports one owner — the correspondence failing, not the model
being wrong.

**Monotonicity held only for adjacent readings.** The clock fix related a reading to the previous
*sample*, but the other six axioms left that sample unconstrained: a mutex call between two readings
could reset it, and the second reading's bound — "never behind the previous sample" — was then vacuous.
Any budget with a bridged operation between its start and end readings could conclude nothing. The fix
adds `World.SameClock` to the six non-clock contracts, and `readings_monotone_across_a_call` is the
guard: a reading, a lock, a reading, and the inequality between them, which did not follow before.

## Testing the dynamics

The contracts cannot be executed: they quantify over an `opaque` relation, so no test observes their
dynamics. Two things *can* be observed, and between them they are the whole of the direct evidence:

- **the model's dynamics**, by `nix develop -c lake exe dynamics` (`LeanIn/Test/Dynamics.lean`) — `World`
  is an executable state machine, so the states the contracts speak about can be enumerated and asked
  for;
- **the primitives' dynamics**, by `nix develop -c lake exe controls` — one control per contract, each
  with its limits stated.

What the first answers is **non-vacuity**: a contract whose hypothesis no reachable state satisfies is
true of nothing. Its output, verbatim, over one lock, one condvar, two threads and sequences of at most
four actions:

```
  hypotheses of the contracts. Each must be reachable, or the contract is true of nothing.
  reachable      A0/A1  a lock is unowned (the state a fresh lock is in)
                   by: (nothing — the initial world already satisfies it)
  reachable      A2/A3/A4  a thread owns the lock
                   by: lock 0 by 0
  reachable      A5  a thread is enrolled on the condvar
                   by: lock 0 by 0 → wait 0 by 0
  reachable      A7  model time has advanced
                   by: tick
  reachable      an empty waiter set is reachable, as `notifyOne_no_waiters` assumes
  reachable      and so is a non-empty one, so that control is not a marker matching nothing
  realisable     the cycle a runtime `wait` spans (same thread, released at the park)
                   by: lock 0 by 0 → wait 0 by 0 → spurious 0 → lock 0 by 0
```

Every hypothesis has a witness, so none of the contracts is vacuous; and the cycle the search finds is
the cycle `World.wait_cycle_reachable` proves, so the search and the proof agree — the cross-check worth
having, since neither is evidence for the other's claim on its own.

**The instrument needed three rounds, and running it found each one.** It first accepted
`lock 1, wait 1, lock 0` as "the cycle" — one thread parking while a *different* thread takes the lock,
so a predicate one thread's acquisition satisfies was standing in for another thread's cycle. It then
reported **nothing at all**, because the trace walker dropped the world preceding each action, so every
path check was aligned against the wrong successor state. It then accepted `lock 0, wait 0, lock 0,
spurious 0`, with the resume arriving *after* the re-acquisition — and the order is part of the claim,
because that is what a `wait` call does.

A probe that reports success for a witness which is not the thing claimed is the same defect class as
everything else in this document, and reading all three would have found none of them. That is the
argument for the instrument existing in the first place.

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

The defects above come from reading the seven axioms, `World.lean`, `Control.lean` and
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

1. ~~What `w'` denotes~~ — decided: (b), recorded above `Runs`.
2. Whether the execution-contract programme enters scope now, later, or not at all.
3. Whether native actor and wait-episode identities belong in the model or only in the bridge.
4. Whether `LeanIn_Bridge_Axioms_Handoff.txt` belongs in the repository at its current path, under a
   name in the repository's style, or outside it.
