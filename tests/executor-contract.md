# The single-carrier executor — behaviour checks

The executor's externally visible promises, checked at its public boundary: the `controls`
executable and an independent pure-model oracle. Nothing here reaches a private function of the
executor. Each check drives the boundary and asserts on the records it produced.

Run one check at a time, from the repository root:

```sh
nix develop -c bash tests/executor-contract.sh SC1
nix develop -c bash tests/executor-contract.sh SC2
nix develop -c bash tests/executor-contract.sh SC3
nix develop -c bash tests/executor-contract.sh SC4
nix develop -c bash tests/executor-contract.sh SC5
```

The fixture is `tests/executor-contract.sh`; the oracle is `tests/ModelOracle.lean`. The shell acts
as the external executable client — its `When` is always an invocation of `controls` and/or the
oracle, never an internal call — and the oracle runs the pure model (`LeanIn.Model.Pool`,
`LeanIn.Model.Scheduler`) so the comparison's expected side is computed rather than written down.

## Records

The `controls` executable reports each executor observation as one line on stdout:

| record | fields |
|---|---|
| `exec\|single\|caller=<tid>\|body=<tid>\|sibling=<tid>\|waker=<tid>\|result=<value>\|order=<events>` | the thread ids of the invoking caller, the awaited task's body, the sibling that must progress on that same caller and the native completion waker of the one observed `blockOn`; the body's returned value; and the events the client recorded for that await, in the order it recorded them |
| `exec\|park\|before=<n>\|after=<n>\|observed=<events>\|queued=<ids>\|delivered=<ids>\|remaining=<n>` | the number of times the pending work completed in each event order, the observed wake events, the ready identities staged before shutdown, the identities whose bodies shutdown actually completed, and the work it left queued |
| `exec\|queue\|staged=<ids>\|phase=<events>\|fifo=<ids>\|lifo=<ids>\|flush=<ids>\|slotBefore=<count:id entries>\|delivered=<ids>\|remaining=<n>` | the identities the client staged at the public queue and scheduling operations, in the order it staged them; the client's own phase events, in the order it recorded them at its actions; the first-phase take receipts of the batch that crossed the ring's capacity; the receipts taken from the LIFO slot; the second-phase receipts after the allowance flushed a pending continuation; the scheduler's own LIFO-slot observation before each of those decisions, keyed by poll count; the identities whose bodies actually ran; and the work left queued |
| `exec\|trace\|<canonical operation record>` | one implementation operation record from the fixed script |
| `exec\|replay\|seed=<seed>\|<canonical trace>` | the canonical trace of one replay of a seed and script |

`staged`, `fifo`, `lifo`, `flush`, `queued` and `delivered` are bracketed comma-separated identity
lists, `[31,32]`; `slotBefore` is a bracketed comma-separated list of `count:id` entries,
`[0:400,1:401]`, each the poll count and the identity the scheduler's LIFO slot held at that
decision. `queued` and `delivered` are the ready identities the client staged before shutdown and the
identities whose bodies shutdown actually completed; each is read as a multiset: the order the bodies
happened to finish in does not matter, while a repeated, missing, unknown or extra id does, and the
count in `remaining` is never a substitute for the identities themselves. `staged` is read as a
multiset for the same reason — the order the bodies ran in is the client's, not the claim — while
`phase` and `order`/`observed` are bare comma-separated event streams, `batch-drained,tick-start`, read
as ordered sequences.
`fifo`, `lifo`, `flush` and `slotBefore` are receipt *sequences*: there the order is the assertion, so
a repeated, missing, unknown or extra entry fails and so does the same entries in another order.
`fifo` and `flush` are also separate phase boundaries: `fifo` carries only the first phase's
receipts and `flush` only the second phase's, so an identity staged into the wrong phase fails its
sequence even when every staged identity is eventually delivered.

A canonical operation record is `op=<name>|pos=<position>|task=<identity>|out=<outcome>`; a canonical
trace is those records joined with `;`, with no leading, trailing or doubled separator. Thread ids,
elapsed time and unrelated stdout are excluded from a canonical trace. The oracle prints one
`model|trace|<canonical operation record>` per step.

The `out` field is the transaction's own outcome, taken from the model:

| `out` | operation |
|---|---|
| `inflight<n>` | a submit or an external enqueue; `n` is the work the pool holds afterwards |
| `taken<n>` | a take that returned a task; `n` is the pool's total taken afterwards |
| `parked<n>` | a park that was granted; `n` is the number of parked carriers afterwards |
| `none` | the operation changed nothing: a park refused while work was held, or a take that found nothing |

The `order` field of an `exec|single|` record lists the events the client recorded for that one await,
each appended by the actor that caused it where it occurred, in the order it occurred:

| event | when the client recorded it |
|---|---|
| `await-registered` | the awaiter registered its continuation and yielded |
| `sibling-done` | the sibling body finished on the invoking caller |
| `gate-released` | the sibling released the fake completion's gate |
| `await-completed` | the awaiter resumed on that caller with its value |

The complete stream is `await-registered,sibling-done,gate-released,await-completed`, so the sibling's
progress precedes the gate release and no event is missing, doubled or unknown. Nothing retypes that
stream from a desired result, and no elapsed time decides the order: the gate is a mutex/condvar
handshake between the sibling and the fake completion.

`observed=<events>` is a comma-separated list of the wake events the client observed, in the order it
observed them:

| event | observation |
|---|---|
| `pre-notify=emitted-before-park` | in the notification-first order, the producer emitted before the carrier parked |
| `pre-notify=completed` | the notification-first wait completed |
| `parked-first=parked` | the carrier had parked before the producer acted |
| `producer=emitted-after-park` | the producer emitted only after that park |
| `parked-first=completed` | the parked-first wait completed |
| `drain=0` | shutdown left no queued work |

These positions are the evidence a check reads. Nothing measures elapsed time to establish a
relation, and the harness watchdog that bounds an invocation is not evidence either: an invocation
that never returns is reported as a defect of the invocation, never as a failure or a pass of a
check.

A check requires exactly one `exec|single|`, `exec|park|`, `exec|queue|` and `exec|replay|` record per
invocation, and as many `exec|trace|` records as the script has steps. Records are parsed by named
key: a key that is absent, repeated or empty fails the check rather than resolving to another field's
value.

A check fails when a record is absent, repeated, malformed, or relationally false, and reports the
check's own `Then` text. A failure before the check's assertion — the executable did not run, the
library did not build, the oracle produced nothing, an invocation never returned — is reported
separately as a setup error.

## The fixed script

Both the executor's trace and the oracle advance the same ordered operations, over the same task
identities, at the same input positions. Every step is one *modelled transaction* rather than a change
to one model at a time: a submit or an external enqueue advances both the pool's `submit` and the
scheduler's `enqueue`; a take that returns a task advances both the pool's `take` and the scheduler's
`take`; a take that finds nothing advances neither. The scheduler's work count and the pool's held
work are then the same quantity after every step, so the two sides' outcomes refer to the same work
rather than to two independent counters, and the two parks mean what they say — refused while two
items are held, granted once both have been taken.

| pos | operation |
|---|---|
| 0 | submit task 0 |
| 1 | submit task 1 |
| 2 | park, with two items held |
| 3 | take task 0 |
| 4 | take task 1 |
| 5 | park, with nothing held |
| 6 | external enqueue task 2, which unparks the carrier |
| 7 | take task 2 |
| 8 | take, with nothing held |

______________________________________________________________________

### SC1 — the awaiter yields to a sibling on the invoking caller before the gated wake

**Actor.** A Lean executable client of LeanIn.

**Boundary.** `nix develop -c bash tests/executor-contract.sh SC1`, which invokes
`lake exe controls --executor-single`.

**Given.** An awaiter whose native completion is held behind a synchronized gate — a mutex/condvar
handshake, not a timer — and a sibling task that must execute on the invoking caller and release that
gate. Until the sibling runs, the fake completion cannot fire.

**When.** The client drives `blockOn`.

**Then.** There is exactly one `exec|single|` record, and its fields are exactly `caller`, `body`,
`sibling`, `waker`, `result` and `order` in that order with nonempty values, so every value is bound
from one parsed invocation rather than from anywhere it appears. In that record `body` equals `caller`
and `sibling` equals `caller` — the awaited body and the sibling both ran on the invoking caller's
thread — `waker` differs from `caller`, `result` is `7`, and `order` is the complete recorded stream
`await-registered,sibling-done,gate-released,await-completed`, in which the sibling's progress
precedes the gate release.

The same order detector is held to its own control inside that invocation: it accepts that complete
stream and rejects two near misses — the same events with the gate released before the sibling
progressed, and the stream a blocking await would leave, in which the sibling never progresses at all.
Those near misses are built from event names alone, never from the executor's output, and a control
that does not hold is a fixture defect reported separately from the `Then`. A record that shows a
value returning with no sibling progress has not shown that the awaiter yielded.

**Why.** An await that blocks the carrier returns the right value on the right thread and still
starves every sibling behind it; the executor's nonblocking claim is that the awaiter suspends and
the caller's own carrier runs the sibling, and the only evidence of that at this boundary is the
sibling's progress recorded before the wake.

______________________________________________________________________

### SC2 — an injected completion wakes a waiting `blockOn`, and shutdown delivers the staged work once

**Actor.** A Lean executable client whose injected completion wakes a waiting `blockOn`, and whose
shutdown drains ready work.

**Boundary.** `nix develop -c bash tests/executor-contract.sh SC2`, which invokes
`lake exe controls --executor-park`.

**Given.** A synchronized fake completion producer that uses a native `Task` only as a waker and two
separate event orders — notification before the waiter parks, and a waiter truly parked before
notification — and, staged ready before shutdown, two known queued identities, `31` and `32`.

**When.** The client injects the events and calls shutdown.

**Then.** In the one `exec|park|` record, `before` and `after` are each `1` — the pending work
completes exactly once in *both* orders — and `observed` reports, in the order the client observed
them, `pre-notify=emitted-before-park` before `pre-notify=completed`, and `parked-first=parked`
before `producer=emitted-after-park` before `parked-first=completed`, together with `drain=0` for a
shutdown that left no queued work. The parked-first completion is thus preceded by the observation
that the carrier had parked and that the producer emitted only afterwards; that order of observations
is the affirmative control, not a timing claim, and the harness watchdog only bounds a hang.

The staged work, not the count, is what the shutdown claim rests on. `queued` is the client's
pre-shutdown staging receipt and `delivered` is the receipts of the bodies shutdown actually ran;
each is read as a multiset of identities and must be exactly `[31,32]`, so a duplicate `31` with `32`
missing, or an empty `delivered` beside a `remaining` of `0`, fails the `Then` rather than passing on
the count. `remaining` must be `0` as well, and it only corroborates the receipts: it can never stand
in for them.

That delivery comparison is held to its own control inside the same invocation: the detector accepts
the staged pair — `[31,32]` and the same identities in the other order — and rejects both an empty
delivery beside `remaining=0` and a duplicated `31` with `32` missing beside `remaining=0`. The near
misses are written from the staging alone, never taken from the executor's receipts, and a control
that does not hold is a fixture defect reported separately from the `Then`.

**Why.** A notification with no waiter is lost, so the state must be checked under the same lock as
the park; the parked-first order is exactly the race that a naive protocol hangs on. Shutdown is the
other half of the same protocol: a drain that reports a zero count while completing nothing, or
completes one item twice, has lost or duplicated work the caller staged.

______________________________________________________________________

### SC3 — implementation operation records match the pure model pairwise

**Actor.** An executable client checking LeanIn's refinement.

**Boundary.** `nix develop -c bash tests/executor-contract.sh SC3`, which invokes the existing
`controls` executable and the oracle.

**Given.** The same fixed scripted operations, input positions and task identities on both sides.

**When.** The client compares the implementation's records from the executable to the independently
computed `Pool`/`Sched` records.

**Then.** The oracle's records are nonempty first, as the comparison's affirmative control. Then for
every record the parsed `op`, `pos`, `task` and `out` fields match pairwise, and each record is
exactly those four nonempty fields, so an extra, omitted, reordered, duplicated, malformed or wrong
record fails rather than being matched by token presence. The failure names the first record that
differs.

The comparison and its controls are one instrument: a single parsed-record comparator that reads
`op`, `pos`, `task` and `out` each from its own record's named field at the same input index and
requires the four to agree. In the same invocation that comparison runs, that one comparator is also
held to its own controls — it positively accepts the oracle's genuine record against itself, and it
rejects two near misses built only from the oracle's own values: that record with its `task` and
`out` values exchanged between those named fields, and that record with its `pos` value replaced by
the oracle's next position while every other field stays plausible. The near misses exercise the
detector alone; they are never implementation records and never stand in for the implementation
whose absence the `Then` reports. A control that does not hold — a comparator that accepted a near
miss, or that rejected a record against itself — is a fixture defect reported separately from the
`Then`, because a `Then` asserted through an instrument that is not comparing named fields would
otherwise pass or fail for the wrong reason. The empty implementation side still fails the `Then`
itself: the model's records against the implementation's none.

**Why.** The refinement claim rests on the executor's transactions agreeing with the model, so a
model-versus-implementation trace mismatch has to be a failing comparison with the differing record
named, not a difference described in prose.

______________________________________________________________________

### SC4 — a staged scripted failure replays identically, and an alternate script differs

**Actor.** An executable client replaying a scripted run.

**Boundary.** `nix develop -c bash tests/executor-contract.sh SC4`, which invokes `controls` twice with
the same seed and scripted inject input and once with an alternate script.

**Given.** Explicit ordered injection inputs, a seed and a script name. The main script carries a
deliberate failing task: task identity `1` fails at input position `3` with the outcome
`error:seeded-failure`. The alternate script delivers identity `2` at that position instead of `1`.

**When.** The client replays the exact seed and scripted input.

**Then.** Each of the three invocations produces exactly one `exec|replay|` record, whose `seed` field
equals the seed given on that command line, and each trace body is a nonempty run of canonical
records — so a missing trace, a retyped seed or a junk body is rejected before anything is compared.
The raw canonical byte traces of the two same-seed invocations of the main script are identical, and
the alternate script's trace differs, so the comparison is not blind. A mismatch reports the first
differing record and the replay inputs.

The failure itself is bound, not merely present. Each of the two main traces must contain exactly one
record with `op=fail`, and that record's own `pos`, `task` and `out` fields must be the staged
`3`, `1` and `error:seeded-failure` — a trace that carries those tokens somewhere else, or a second
failure record, fails. The alternate trace must carry identity `2` in the record at position `3`,
which is the difference the alternate script injects, so the two scripts are distinguished by their
staged identities as well as by their bytes.

The trace checker is exercised inside the same invocation that replays. On a well-formed two-record
canonical trace it must accept the trace and parse it as exactly two records of four fields each,
and it must reject the five near misses of its separator rule: an empty trace, a leading `;`, a
trailing `;`, a doubled `;;` and a lone `;`. The per-record lookup the failure binding reads through
is exercised there too: it finds the single record carrying a named field value, and rejects a value
that no record carries or that two records carry. Those controls are fixture integrity, not the
replay evidence — they show the comparison is made through a checker that can tell a canonical trace
from a malformed one, and that binds a record by its own field — and they neither replace the replay
execution nor satisfy the `Then` above. A control that does not hold is reported separately from the
`Then`, as a defect of the fixture.

**Why.** Deterministic replay is the executor's debugging contract: a failure seen once has to be
reproducible from its inputs, which is only meaningful if the replay reproduces that failure at its
own position and identity, and if a genuinely different script is observed to produce a different
trace.

______________________________________________________________________

### SC6 — real work runs on one carrier, and a pool worker only ever enqueues

**Actor.** A Lean executable client running a program on the single-carrier runtime.

**Boundary.** `nix develop -c bash tests/executor-contract.sh SC6`, which invokes
`lake exe controls --runtime-threads`. The client drives `Runtime.blockOn` on the thread it was started on,
and reads the thread identity *inside* every step the runtime ran.

**Given.** A fresh runtime, and a program that spawns a child, awaits it, awaits a second value delivered by a
stock `Task` completing on a pool worker, and reads its own thread identity in each body.

**When.** The client drives the runtime on the calling thread until the program's value arrives. No
`IO.asTask` in this mode belongs to the runtime; the one that exists is the external completion.

**Then.** There is exactly one `exec|runtime|` record, and its fields are exactly `caller`, `steps`,
`external`, `value` and `remaining` in that order with nonempty values.

`steps` is the thread each task step ran on, in order, and **every entry equals `caller`** — the driver, the
spawned child's body and the continuation that resumed after the external completion are one thread.
`external` is the thread the completion ran on and is **not** `caller`: the measurement is not vacuous,
because a second thread was in the picture, was observed, and only enqueued. `value` is the program's own sum
of what the child returned and what the external completion delivered, and `remaining` is 0.

The "every step ran on the carrier" detector is exercised inside the same invocation: it accepts a step list
of one thread and rejects a list carrying another, which is the near miss a runtime that quietly handed a body
to the pool would produce. A control that does not hold is a fixture defect reported separately from the
`Then`.

**Why.** "One carrier" is a claim about where our code runs, and a thread identity is the only way to check it
from outside. It is worth separating from "there is only one thread": the external completion genuinely runs
elsewhere — that is what the O3 bridge is for — and what this check asserts is that nothing *of ours* runs
there.

______________________________________________________________________

### SC5 — the bounded ring, the LIFO allowance and the overflow keep every staged identity

**Actor.** A Lean executable client of LeanIn's public queue and task scheduling operations.

**Boundary.** `nix develop -c bash tests/executor-contract.sh SC5`, which invokes
`lake exe controls --executor-queue`. The client stages, takes and locally spawns work through the
public queue and scheduling operations only — it writes no ring, slot or counter of its own — and the
check reads no private state either: it reads the receipts that client recorded at those operations.

**Given.** A fresh queue, the distinct staged identities `0..256`, `300`, `301` and `400..403`, and
one ordered script of two phases. In the first phase the client submits all of `0..256` before taking
any and then drains that whole batch: the 257 submissions fill a 256-slot ring, so the last of them
crosses its capacity, and the batch's take receipts are the older half the ring kept and the identity
that crossed it, followed by the newer half the overflow moved to `inject`. The second phase is a fresh tick that begins only once the first batch
has been drained: there the client stages `300` and `301` as FIFO queue work, and the root client
locally `spawn`s `400` through the public scheduling operation, and each executing body locally
`spawn`s the next of `401..403`, so those four continuations become ready on the current worker in
that tick. Local `spawn` is the operation that enqueues ready work on the current worker and wakes
it; the worker's `wake` operation un-parks only and places no work, so a slot populated through
`wake` is not this check's subject — and a client that wrote ring, slot or counter itself would not
be exercising the public operations at all.

**When.** In one scripted invocation the client first submits the 257 identities of `0..256` and
drains that whole batch, then, in a fresh tick after that drain, stages `300` and `301` and drives the
chained local spawns in that tick, recording each phase event at the action that produced it — the
drained batch, the fresh tick, the two stagings, the root spawn — alongside each identity where it
stages or spawns it, each identity from inside the body that runs it, each take receipt where the take
returned it, and each slot observation from the scheduler at the decision itself — never from a list
of what it expected to see. The ordered script is the sole source of the two phases' order; no clock
or sleep decides it.

**Then.** There is exactly one `exec|queue|` record, and its fields are exactly `staged`, `phase`,
`fifo`, `lifo`, `flush`, `slotBefore`, `delivered` and `remaining` in that order with nonempty values,
so every value is bound from one parsed invocation rather than from anywhere it appears.

`phase` is exactly `batch-drained,tick-start,stage:300,stage:301,spawn:400` — the client's own events,
in the order it recorded them where they happened. `batch-drained` is recorded only after all 257 of
the first batch's takes have returned their receipts, `tick-start` marks the fresh tick, `stage:300`
and `stage:301` are the two FIFO stagings in that tick and `spawn:400` is the root local spawn. The
stream is read as an ordered sequence, so a stream carrying the same five events with either staging
ahead of `batch-drained` — the early staging this assertion exists to catch — fails here even when the
first batch's `fifo`, the slot observations and the final `staged` and `delivered` sets all look
right.

`fifo` is exactly `0..127,256,128..255` — the take receipts of the batch that crossed capacity. That
is the model's own rule: `cap` is 256 and the placement rule `Pool.submit` uses keeps the older half of
a full ring while moving the *newer* half to `inject` (`LeanIn/Model/Pool.lean:52,119-125`), so the
257th submission of `0..256` leaves the ring holding `0..127` and the new `256`, and `inject` holding
`128..255`; and `Pool.take`'s `takeFromRing` serves the ring before `inject` (`:81-86`), so the receipts
run `0..127` and then `256`, followed by `128..255`. The expected order is read from the model's rule rather than from the implementation's
output, and it is read as a sequence: those identities in another order fail here. Because `fifo` is
the first phase's own receipt boundary it carries no `300` and no `301` — the script stages those two
only in the second phase — so a client that staged either of them before the first batch was drained
would record it among these receipts and fail here, even though both identities are delivered later
and `staged` and `delivered` still hold all 263.

`lifo` is exactly `400,401,402` and `flush` is exactly `300,301,403`. `lifoCap` is 3 (`:54`) and
`Pool.take` polls the LIFO slot while the tick's allowance lasts, flushing a slot that is still
occupied once the allowance is spent (`:94-102`); so the three chained continuations are polled from
the slot, the pending `403` is flushed to `inject` when the allowance is exhausted, and the ring is
then served — `300`, `301` — before the flushed `403`. A fourth poll of the slot in place of that
flush fails here, and because `flush` is the second phase's own receipt boundary it stays separate
from the `fifo` receipts of the first phase.

`slotBefore` is exactly `[0:400,1:401,2:402,3:403]` — the scheduler's own slot observation taken at
the decision itself, before each of the three polls and before the flush, keyed by the poll count. It
is the record the scheduler produced at that instant, not a value the client retyped from the
expectation, so an implementation that never populated the slot would have to record `-` and fail
here; the first three entries are nonempty identities at poll counts `0`, `1` and `2`, and the fourth
is nonempty at count `3` immediately before the flush. That is what makes the allowance observable
rather than assumed: the populated slot the three polls read is the local `spawn` operation's own
effect, and an always-empty slot cannot produce this sequence.

`staged` and `delivered` are read out of their own named fields as multisets of identities and must
each be exactly the 263 staged identities, once each: an identity duplicated with another missing, an
unknown identity, or work left behind (`remaining` must be `0`) fails. `remaining` only corroborates
the receipts, and never stands in for them.

Those detectors are held to their own control inside the same invocation. The multiset detector
accepts the full 263-identity set and rejects a staged/completed set carrying one identity duplicated
and another missing. The one sequence detector accepts the modelled `fifo`, `lifo`, `flush` and
`slotBefore` orders and rejects four near misses — the pair either side of the capacity crossing
exchanged, a `lifo` that took `403` as a fourth poll in place of the flush, an always-empty slot
`slotBefore=[-,-,-,-]` that only a vacuous allowance test would accept, and a first-phase `fifo` whose
receipts carry `300` and `301`, which is what a client that staged them before the first batch was
drained would record. The phase detector accepts the ordered stream and rejects the same five events
with `stage:300` and `stage:301` recorded before `batch-drained`, so a run that staged the two
identities early fails on the phase order even after every token has arrived exactly once. Every near
miss is built from the expectation or the record syntax alone, never from the executable's receipts,
and a control that does not hold is a fixture defect reported separately from the `Then`: a detector
that accepted any near miss, or that rejected the modelled order, has not asserted this `Then`.

**Why.** The queue's promise is that a staged item is held until it is taken, and that the LIFO
allowance is a policy which can never strand work; local `spawn` is what makes that allowance
reachable, by placing the spawned continuation in the slot, while the worker's `wake` only un-parks a
worker and places no work. A ring that drops the half it cannot hold when it overflows, or an allowance that
never saw a populated slot or keeps polling past its cap and leaves the pending continuation behind,
still reports plausible receipts — while losing exactly the work the caller staged. The two phases
keep those receipts honest: a first batch that already carried `300` or `301`, or a `flush` reached
without a fresh tick after the drain, would still deliver all 263 identities while the boundary this
check names was never crossed. The `phase` stream binds that boundary to the client's own actions, so
a run that staged `300` and `301` before the drain cannot pass on a correct-looking batch and identity
set.
