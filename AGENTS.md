# Repository test decisions

## Lean controls and behavior checks

- Use the pinned toolchain with `nix develop -c lake build` to
  compile library, model, proofs and executables. A build is not
  evidence that runtime behavior or the Lean source-to-IO
  correspondence is proved.
- Follow the executable-control idiom in `LeanIn/Test/Control.lean`
  and `Controls.lean`: run `nix develop -c lake exe controls` for
  primitive bridge observations, retain each control's stated
  limits, and observe the executor through a public executable
  client rather than writing its queue internals. The model side has
  its own probe: `nix develop -c lake exe dynamics`
  (`LeanIn/Test/Dynamics.lean`) reports whether each contract's
  hypothesis is reachable, which is the non-vacuity check a proof
  cannot make about itself. A path claim needs a predicate that
  requires the *same* actor at both ends and the stages in order --
  three versions of the cycle predicate were wrong, and each was
  found by running the probe, not by reading it. Add a violation
  check before the fix it is meant to detect: the waiter invariant's
  check reported a duplicate enrolment within four actions before
  the model closed it, which is what makes the later clean run
  evidence rather than a claim.
- Put externally observable executor scenarios in
  `tests/*contract.md` and their executable checks in the
  adjacent shell fixture. Run an individual check with
  `nix develop -c bash tests/executor-contract.sh SC1`,
  substituting a documented scenario ID as needed. The shell
  invokes the public `controls` executable; `tests/ModelOracle.lean`
  independently computes the pure-model side. No new framework.
- In each scenario name the actor, an external boundary and the
  observable outcome. Stage data and record actual actions where
  they happen; bind compared values to their record's named fields,
  not token presence. An assertion red must be the scenario's
  own outcome assertion on unfixed behavior, not a missing import,
  malformed fixture, skip, timeout or invocation error. An
  absence detector needs an affirmative control with that same
  detector in the same run; an edge-state control must name the
  public operation that populates the state it inspects.
- No scenarios or unit controls reach network services, language
  models or a live clock. Use synchronized fakes for external
  completion and ordered scripted inputs for replay. A watchdog
  bounds a hang but cannot establish timing or causality;
  empirical controls keep their stated limits.

## Proof and trusted-base audit

- Keep pure-model obligations and executable controls separate.
  Show *reachable* positive and negative witnesses for model
  states: the LIFO slot must be populated by local `spawn` before
  its poll/flush properties can be claimed, not hand-filled in
  an unreachable example. Local completion of a value awaited
  by another task on the carrier (or cooperative yield) uses
  queue push / `Pool.submit` (FIFO), not the LIFO slot; external
  completion uses inject. All producers go through one internal
  scheduling-destination decision. Check `#print axioms` for each new
  theorem, and know what it does not see: an assumption stated as
  an `opaque` predicate has a hidden value and is not an axiom, so
  `#print axioms` never names it. Visibility
  is not content, though: an `axiom` predicate is named and can
  still say nothing, entailing nothing -- which is how a comment
  claiming injectivity sat beside a declaration that entailed no
  such thing, and two runtime objects aliased one model index.
  Write the proposition you actually need, as a definition with
  content, and require it where it is used. No `sorry`, invented
  serializability axiom or claimed end-to-end Lean-IO theorem
  substitutes for a proof.
  Compare scripted executor records with independently computed
  model records and fail on the first mismatch.
- After runtime source exists, search implemented `LeanIn/Task`,
  `LeanIn/Sched`, `LeanIn/Runtime` and imports for direct external
  operations and stock `Task`/`Promise` call paths. Reconcile
  them with the primitive register in `docs/decisions.md`,
  citations/controls in `docs/primitive-theory.md` and
  `LeanIn/Theory/Bridge.lean`, and the trusted-base table in
  `docs/proof-strategy.md`. Name direct separately assumed
  operations as primitives with citations and controls;
  name transitively reached promise machinery as trusted
  substrate. A direct `IO.Promise` call requires its own
  cited primitive and control. A text search cannot rule
  out aliases or indirect imports: inspect calls and import
  edges as well. No source-level end-to-end IO theorem exists.
