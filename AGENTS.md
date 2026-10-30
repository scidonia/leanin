# Repository test decisions

## Lean controls and behavior checks

- Use the pinned toolchain with `nix develop -c lake build` to
  compile the library, the model and the proofs. The executables are
  not default targets -- every one of them links the socket shim, so
  building one needs libuv -- and are built on demand:
  `nix develop -c lake exe controls`, `nix develop -c lake exe server`.
  A build is not
  evidence that runtime behavior or the Lean source-to-IO
  correspondence is proved.
- The flake's `lean4` is the official binary release for the version
  `lean-toolchain` names (`v4.35.0`), fetched from `releases.lean-lang.org`
  and patched into the store; a store that lacks it downloads the tarball,
  it does not compile Lean. Where the flake cannot be used, run the same
  commands with the toolchain `lean-toolchain` names, which `elan` provides
  at the same version, and say which of the two ran.
- Follow the executable-control idiom in `LeanIn/Test/Control.lean`
  and `LeanIn/Exe/Controls.lean`: run `nix develop -c lake exe controls` for
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
- Bridge contract scenarios live in `tests/bridge-contract.md` with
  their executable checks in `tests/bridge-contract.sh`, driven at
  the public `bridgecontrols` executable: run one with
  `nix develop -c bash tests/bridge-contract.sh BT1` (also BT2, BT3).
  A scenario's synchronization must not depend on which thread wins
  a race, and the way to check is to run it repeatedly: BT2's first
  two designs hung intermittently because a waker looping over two
  episodes could spend the second notification before the second
  wait had started. Start each synchronizing actor while the lock is
  held, and give it one job. Records are
  the carriers' own annotations, because the primitives have no
  observation hooks, so such a scenario can state ordering and
  ownership and cannot see anything a carrier does not name. A
  trace test can falsify a contract and cannot establish adequacy,
  and must say which. Mutations that exercise the checker must
  change a *field*: it addresses records by field, so reordering
  lines changes nothing and must be accepted, and a mutation that
  changes nothing is reported rather than counted as a pass.
- Lifecycle deadlines have their own focused checks: `nix develop -c bash
  tests/stop-deadline.sh` (a scoped 60 s `VM.sleep` aborts at a 100 ms stop deadline),
  `nix develop -c bash tests/drain-deadline.sh` (a client's handler is parked in a 60 s
  sleep; the accept loop's 100 ms drain deadline cancels it and the loop returns), and
  `nix develop -c bash tests/scope-cancel.sh` (a user cancel retires a parked sleep
  immediately, a child scope is cancelled with its parent, and cleanup runs exactly once).
  All assert elapsed time or counts, so a hang or a double cleanup fails rather than passes.
- Multi-carrier serving: `nix develop -c bash tests/multi-carrier.sh` (64 shared tasks land on at
  least two of three carriers) and `nix develop -c bash tests/multi-server.sh` (`server workers=2
  count=8` answers every connection and exits). The server check uses a unique port and a finite
  batch; `waitFinished` must not park on the carriers' condition variable, or `notifyOne` can wake
  the caller instead of a worker.
- Queue scaling: `nix develop -c bash tests/queue-scaling.sh` times the inject and the timer hand-off at
  two depths in one process and fails if ns/op rises with depth; a copying `Array` on a shared cell is its
  affirmative control, and exit 2 means that control was not flagged. It is a timing check, so it reads the
  clock the scenario rule below excludes, and it keeps an empirical control's limits: it can falsify "cost is
  independent of depth" and cannot establish it. Functional laws cannot see this: `Deque`'s held throughout
  while every operation copied the store. Anything unbounded held in a `Std.Mutex` or a global needs a case
  here, because a value stored in a shared cell is marked, a marked `Array` is never exclusive, and releasing the
  cell's own reference does not change that.
- The stock-handler adapter has a pure check: `nix develop -c bash tests/compat-handler.sh`
  (a stock handler reads the buffered body, adds a header, and the adapter maps its response).
- The `Std.Http`-shaped handler layer (`LeanIn/Http/StdHandler.lean`, D24) has socket scenarios in
  `tests/std-handler-contract.md`: `nix develop -c bash tests/std-handler-contract.sh SH1` (also
  SH2–SH7), driven at the public `stdEcho` executable, with a unique port per run (`STD_PORT`). Its
  date formatter has a pure check: `nix develop -c bash tests/std-date.sh`.
- The generic handler contract is a compile-time witness for both hosts:
  `nix develop -c lake build LeanIn.Test.HandlerContract` (one middleware and one body helper, stock and
  LeanIn instantiations).
- VM catch/finalizer semantics have a focused check:
  `nix develop -c bash tests/vm-scope.sh` (lexical catch scope; finalizer exactly once on
  success, ordinary error, abort, and finalizer failure).
- The H1 target views have a pure check: `nix develop -c bash tests/h1-target.sh`
  (`H1.Head.path?`/`query?` decode percent escapes and reject a malformed one).
- Put externally observable executor scenarios in
  `tests/*contract.md` and their executable checks in the
  adjacent shell fixture. Run an individual check with
  `nix develop -c bash tests/executor-contract.sh SC1`,
  substituting a documented scenario ID as needed. The shell
  invokes the public `controls` executable; `tests/ModelOracle.lean`
  independently computes the pure-model side. No new framework.
- The HTTP cancellation contract moved with LeanIO to `scidonia/leanio`
  (`tests/http-cancel-contract.*`, `leanioCancelContract`); LeanIn keeps
  `tests/http-stream.sh` for the stream handler itself.

- The timeout cancellation contract is `tests/timeout-cancel-contract.md`
  with `tests/timeout-cancel-contract.sh`: run
  `nix develop -c bash tests/timeout-cancel-contract.sh TC1`. It drives its
  own `lake exe controls --runtime-time-loser` mode — one carrier, fresh
  `HarnessClock`s, no live clock, no socket — and reads the executable's
  `timeoutLoser|` record for the computation whose `withTimeout` deadline
  won. The recorder's `after` action is run and the same detector reads the
  marker while it is present before the loser is read for its absence, and
  eight record near misses are rejected by that detector in the same
  invocation. Exit 2 is a setup failure (build, an absent or repeated
  record, a false affirmative control); exit 1 is the scenario's own Then.
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
  scheduling-destination decision. At P carriers the same rule has
  a per-obligation **witness idiom**, so a non-vacuity check is
  written through a real transition rather than the state
  hand-filled: `pushShared` (an external wake) before the shared
  half's live obligation, `pushLocal` (the owner is not parked)
  before `ZeroParked`, `flushLocal` (a spent allowance that
  re-queues) before `InjectWatched`, and `stealInto` (the thief
  takes one) before the conservation law. The implementation's own
  wake rules are the other half: a push into the owner's own queue
  owes no wake when the owner makes it, but a `Join`-cell
  continuation (`Async.await`/`select`) runs on whichever carrier
  resolved the cell, so the per-worker `poked` flag with the
  broadcast is the standing mechanism for that third off-owner
  site, and the two seam completions take `Ctx.resumeShared`.
  Check `#print axioms` for each new
  theorem, and know what it does not see: an assumption stated as
  an `opaque` predicate has a hidden value and is not an axiom, so
  `#print axioms` never names it. The list it
  prints is dependencies, not hypotheses: a lemma carrying a local assumption such as
  `Rep.NonAliasing` prints the same list either way, so an axiom-free line means
  "nothing was assumed as an axiom", never "nothing was assumed". Visibility
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
- Prefer a directed `rw` or a `by_cases` to `simp` on
  contract-shaped goals. `simp` rewrites one `if` and not the
  other, leaving two sides that print identically and will not
  close because they differ in the `Decidable` instance behind
  the `if`; resolving the condition first sidesteps the instance
  matching. Learned three times in one session, once per file.
  Check a declaration's naming convention rather than inferring
  it, too: `LeanIn/Data/Ring.lean` name-extends its definitions
  (`Ring.push`) and leaves its theorems bare (`push_toList`), so
  a use site cannot name one by the other's rule.
- Anything holding a `Pool` needs `[Inhabited α]` in scope: `Pool`
  is built on `Ring`, and `Ring`'s operations need it because
  `toList` falls back to `default`. Carry it with one `variable`, as
  `Sched/Pool.lean` and `Sched/Executor.lean` do; adding it per
  declaration produces a page of cascading synthesis failures.

## Performance records

- Every performance number in `docs/PERFORMANCE.md` or the README states the
  commit it was measured on, in the text next to the number (for example
  "measured on `41943fa`"). A number without a commit is not a record.
- Each run entry names, at minimum: the commit, the date, the command that
  produced it (`bench/paired.sh`, `bench/threeway.sh`, `bench/screen.sh`, a
  callgrind invocation with its request count), the levels and load shapes,
  the host load average, the observed results, and the keep/reject/inconclusive
  decision for any change the run evaluates.
- Corrections do not erase the old number: record it as withdrawn, with the
  commit that supersedes it and why (a counter, a control, a rerun).
- A comparison that supports a claim is paired and interleaved in one
  invocation, as `bench/paired.sh` does; a single reading may illustrate a
  shape but not support a ratio.
- The README carries the short table and cites the commit its numbers came
  from; method, ranges and rejected attempts stay in `docs/PERFORMANCE.md`.
LeanIO lives in its own fork, `scidonia/leanio`; its native suite and benchmark run there, not in this
repository. LeanIn's own HTTP examples are checked by `tests/executor-contract.sh SC20` and the
`http-cancel-contract` scenarios, which now drive LeanIn's stream handler directly.

- After touching the shim's raw completion registry (`c/netuv.c`,
  `LeanIn/Runtime/Io.lean`), run `nix develop -c lake exe controls
  --raw-registry` with `NETUV_RAW_CHECK=1`. It checks register/take,
  no double take, replace, withdraw and that the live count returns to zero.
  The ownership, threading and marking argument is
  `docs/notes/LeanIn_RawRegistry_Theory.md`.
