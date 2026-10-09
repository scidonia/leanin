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

### SC14 — the service's own obligations: no drop, a live bound, and resolution within a deadline

**Actor.** A Lean executable server (`lake exe controls --runtime-service`): an accept loop of ours
plus a per-connection body, run on one carrier, with `Std.Async`'s client as the peer. The promises a
client sees are the connection's fate and the request's answer, and they are named by
`LeanIn/Model/Service.lean`'s `Service.NoDrop`, `Service.Bounded`, `Service.RequestsResolved` and
`Service.PendingWithinLive`. Nothing here calls a private function: the client speaks TCP to the
server's own bound socket, and the check reads the executable's stdout and its exit status.

**Boundary.** `nix develop -c bash tests/executor-contract.sh SC14`, which invokes
`lake exe controls --runtime-service --bound=2` three times and asserts on the one `service|` record
each invocation prints, plus the mode's own `servicectl|` checker readings. Every compared value is a
named field of that record, read by key; an absent, repeated or empty field fails the check rather
than resolving to a neighbouring value.

**Given.** A fresh single-carrier executor (`Sched.Executor.new LeanIn.Task.Item 256 1`), a listener
bound to `127.0.0.1:0` (`Runtime.loopback 0`), a bound `B = 2`, and `n = 5` connections whose payload
is one byte, the connection's id. The client stages connection identities `0..4`; the body's response
is staged per id: id `1`'s response is `Runtime.never` (`LeanIn/Runtime/Time.lean:36`), so its deadline
fires rather than its response; id `3`'s response fails with a staged error, so it terminates without
completing; ids `0`, `2`, `4` echo and complete. The client sends the staged ids `1` and `3` last.

**When.** In one invocation: the loop starts the server, the client connects all five sockets and
sends each id, and — before reading or closing anything — waits on the mode's `Std.Mutex`-guarded
admission log until it holds the begins the loop's admission policy requires: `B` begins on a loop
that admits `B` and waits on a permit, every offered begin on a loop that admits unconditionally. It
then reads each admitted socket's reply in that log's order and closes it; the body that owns a closed
socket ends, so the read order is the server's own begin order and not the OS's connect order or a
scheduler race. The loop drains and returns when every body has ended, and the mode prints the
`service|` record and its `servicectl|` readings.

**Then.** There is exactly one `service|` record, and its fields are exactly, in this order with
nonempty values: `bound`, `offered`, `accepted`, `completed`, `closed`, `liveHighWater`,
`parkedAtPeak`, `requests`, `responded`, `errored`, `deadlineFired`, `carrier`, `runUs`. The three
obligations are read from their own named fields, each in the multiset or inequality the model
statement names:

- **SC14-O1** — `Service.NoDrop`: `completed ∪ closed`, as an id multiset, equals `accepted`. The
  affirmative control, read from the same record, is that `completed` and `closed` are both nonempty, so
  the equality is not carried by one path alone. That union equality and those two nonemptinesses are
  the whole of the assertion: `accepted`'s own value (`[0,1,2,3,4]` here) and `offered` are printed but
  never asserted, and neither terminal list is compared against a named id.
- **SC14-O2** — `Service.Bounded`: `liveHighWater ≤ bound`, and the affirmative control
  `liveHighWater = bound`. `parkedAtPeak` is the mode's second reading of the same count, from its own
  running annotation, and reads `bound` too.
- **SC14-O3** — `Service.RequestsResolved` and `Service.PendingWithinLive`: `responded ∪ errored`, as
  an id multiset, equals `requests` disjointly, so every request id is resolved exactly once and none
  is outstanding. The affirmative controls, in the same record, are `deadlineFired = yes` (id `1`'s
  request was resolved by the deadline transition) and `responded` and `errored` both nonempty.

`runUs` is printed and never asserted; `carrier` and `offered` are recorded, not asserted. The record
is a set of order-independent equalities and one inequality, because the order bodies finish in belongs
to the scheduler: `completed`, `closed`, `responded` and `errored` are compared as multisets, and
`accepted`/`requests` are printed in ascending id order.

**The failure this scenario records on the shipped loop.** The accept loop in the tree as it stands
admits every offered connection — one accepted socket and one spawned body each, with no admission
bound. The mode's body therefore drives that loop, and `SC14-O2`'s `liveHighWater ≤ bound` is false:
the record carries `liveHighWater=5` and `parkedAtPeak=5` against `bound=2`, and the check exits 1 with
its own `Then` text:

```
SC14 Then: the live-connection bound is not held
  obligation: every live connection is within its bound (Service.Bounded)
  expected liveHighWater <= bound=2 and liveHighWater = bound
  observed: liveHighWater=5 parkedAtPeak=5 accepted=[0,1,2,3,4]
```

The violation is already in the shipped loop, so no staged revision, no ordering deviation and no
substitution exposes it. `SC14-O1` and `SC14-O3` hold on the same loop: the unbounded loop awaits
every spawned body, and the body reports `.ok` for a completed connection and an error for one that
deadlines or fails, so the id partition and the disjoint resolution both hold. Those two clauses and
`SC14-O2` are each evaluated on the record before the first failing one is reported, so a run that
also broke either of them would name it instead. A red is only a red if it is this clause's own
assertion: a missing `service|` record, a malformed record, a non-zero exit without a `fail` line, or a
watchdog expiry is a setup error, not the `Then`.

**Why, and what it rests on.** `Service.NoDrop` is the partition "every admitted connection appears
exactly once, in exactly one of live/completed/closed", so obligation 1 asks the executor's record to
show that partition for the ids it admitted, and the affirmative control is that both terminal paths
are populated rather than one carrying the whole equality. `Service.Bounded` is `live.length ≤ bound`,
and its executor counterpart is the live high-water over the mode's own `begin`/`end` annotations; the
client's deferral of every read and close until the loop's admission policy is satisfied — `bound`
begins on a loop that waits on a permit, every offered begin on one that admits unconditionally — is
what makes `liveHighWater = bound` on the bounded loop, structural rather than a timing accident
**because the client connects the self-terminating ids `1` and `3` last**: the first `bound` admissions
are therefore the echoers, which cannot end before the client's deferred first close, so the high-water
is exactly the bound; the same deferral on the unconditional loop admits all five at once, which is why
the equality is absent there. This rests on the accept queue delivering accepts in the client's connect
order — an ordering assumption, not a fact the scenario establishes. `Service.RequestsResolved` is
`responded + errored + pending.length = requests` and `Service.PendingWithinLive` keeps every pending
request on a live connection, so obligation 3 asks the record to resolve each request exactly once, and
the deadline path is exercised by id `1`'s `Runtime.never` response — an event order, not a clock: the
deadline fires with no dependence on the peer. On the shipped loop, `liveHighWater` is the offered
count, which is the bound violated, and the other two obligations are what the run still shows, which
is what makes the record evidence for all three rather than only for the clause that fails.

The checker is exercised inside the same invocation: it accepts a well-formed record and rejects near
misses whose `completed` is missing an id `accepted` holds, whose `closed` carries an id `completed`
also carries, whose `liveHighWater` is `bound + 1`, whose `liveHighWater` is `0`, whose `requests`
carries an id in neither `responded` nor `errored`, and whose `deadlineFired` is `no` with `errored`
empty. Every near miss is built from the record syntax and the expectation, never from the mode's
output, and a control that does not hold is a fixture defect rather than this `Then`. The mode's own
`servicectl|` readings must hold too: on a well-formed record the checker says `accepted`, and on each
near miss it says `rejected`. The `Then` must hold in each of the mode's three invocations.

______________________________________________________________________

### SC13 — async synchronisation: a mutex, a semaphore and a bounded channel on one carrier

**Actor.** A Lean executable client of the task layer (`lake exe controls --runtime-sync`), driving the
three primitives of `LeanIn/Task/Sync.lean` — an async mutex, an async semaphore and a bounded channel —
from computations on one `Sched.Executor.new LeanIn.Task.Item 256 1`, with `Runtime.Hooks.new` for the
fake completions.

**Boundary.** `nix develop -c bash tests/executor-contract.sh SC13`, which invokes
`lake exe controls --runtime-sync` three times and asserts on the one `sync|` record each invocation
prints, plus the mode's own `syncctl|` checker readings. Nothing here reads a private field, a queue or a
slot: every compared value is a named field of that record, and every event in its `order` field was
appended by the actor that caused it, where it happened.

**Given.** A fresh executor (`Sched.Executor.new LeanIn.Task.Item 256 1`) and a fresh `Runtime.Hooks.new`.
Two `IO.Promise (Except IO.Error Unit)` gates, resolved only by the unrelated computation's own steps — a
mutex/condvar-shaped handshake, never a timer — and a third such gate which the second holder resolves at the
start of its step, so the unrelated computation's first step is caused while the first holder still holds the
mutex. `Sync.Mutex.new`; `Sync.Semaphore.new 0` for the parked acquirers; `Sync.Channel.new k` for a bound `k`
with `sent = k + 1`, and a second `Sync.Channel.new sent` as the affirmative control. The carrier's tid is read
on the mode's own thread.

**When.** One invocation, inside one `Runtime.run`. The first holder acquires the mutex, records
`a-enter`, spawns the second holder and the unrelated computation, and awaits the first gate. The second
holder records `b-enter` only after it is granted the mutex, spawns the unrelated computation's second
step inside its own section, and awaits the second gate. The unrelated computation's first step waits on the
third gate, records `u` and releases the first gate — the only wake that ends the first holder's section — and
its second step, spawned only from inside the second holder's section, records `u` and releases the second
gate. Both holders return their own value. Then, on the channel of bound `k`: `sent` non-parking `trySend`s,
then `sent` `send`s against the full channel, each drained by a `recv` (which the parked senders wait on),
then the control channel, capacity `sent`, `sent` `trySend`s. Then the semaphore's permits: two
`tryAcquire`s, a third, one `release`, and a fourth. Then the three cancellation laws, each read from a
non-parking probe:

1. a holder takes the mutex, a waiter parks on it, the waiter is cancelled, the mutex is released, and a
   non-parking `tryLock` reads whether the permit is still there;
2. a receiver parks on an empty channel, is cancelled, one value is sent, and a non-parking `tryRecv`
   reads whether the value is still there;
3. a sender parks on a full channel, is cancelled, one value is drained, and a non-parking `trySend`
   reads whether a slot is free and whether the cancelled sender's value has appeared.

The second law's probe follows a stock completion scheduled after the send, because the receiver's value
is taken by the receiver's own stock task and that task runs on the pool; the wait is a completion, not a
clock. The mode then prints the `sync|` record, its `syncctl|` readings and its `syncbench|` line, and
returns.

**Then.** There is exactly one `sync|` record, and its fields are exactly, in this order with nonempty
values: `cap`, `order`, `aResult`, `bResult`, `sent`, `tryAccepted`, `tryRejected`, `parkedDelivered`,
`controlAccepted`, `controlRejected`, `semAccepted`, `semRejected`, `semAfterRelease`,
`cancelLockAcquired`, `cancelRecvValue`, `cancelSendGhost`, `cancelSendAccepted`, `runUs`. Records are
parsed by named key; a key absent, repeated or empty fails the check rather than resolving to another
field. `order` is a comma-separated event stream read as an ordered sequence of exactly the six events
`a-enter`, `a-exit`, `b-enter`, `b-exit`, `u`, `u`, once each; the order of the two sections relative to
each other is not asserted, and `aResult`/`bResult` are distinct values the holders returned.

**Both holders complete, and their sections do not overlap:** `aResult` and `bResult` are nonempty and
distinct, `a-enter` precedes `a-exit` and `b-enter` precedes `b-exit`, and one section lies wholly before
the other — read from the events' positions, never by comparing the whole stream to a fixed string. **An
unrelated step does not wait:** a `u` falls strictly between the first section's `-enter` and its
`-exit`. **The bound holds, exactly:** `sent = cap + 1`, `tryAccepted = cap`, `tryRejected = 1`, with the
affirmative control `controlAccepted = sent`, `controlRejected = 0`. **Every parked send is delivered:**
`parkedDelivered = sent`. **The semaphore's permits are exact:** `semAccepted = 2`, `semRejected = no`
(a third acquirer is refused), and one release admits exactly one more (`semAfterRelease = yes`). **The
cancellation law holds for each primitive:** `cancelLockAcquired = yes` (a cancelled lock waiter is not
granted the lock), `cancelRecvValue = present` (a cancelled receiver consumes no message), and
`cancelSendGhost = absent`, `cancelSendAccepted = yes` (a cancelled sender consumes no slot). `runUs` is
printed and never asserted on.

The checker is exercised inside the same invocation: it accepts a well-formed record and rejects near
misses whose `order` overlaps, whose `u` falls outside both sections, whose holder values are empty or
equal, whose accepted count is one short of the bound, whose control rejected a send, whose admitted
permit count is one, whose release admitted no one, whose cancelled lock waiter was granted, whose
cancelled receiver consumed a message, whose cancelled sender consumed a slot, and a record with nothing
to observe. Every near miss is built from the record syntax and the expectation, never from the mode's
output, and a control that does not hold is a fixture defect rather than this `Then`. The mode's own
`syncctl|` readings must hold too: on a record whose named relation is broken the checker says
`rejected`, and on a well-formed record it says `accepted`. The `Then` must hold in each of the mode's
three invocations.

**Why, and what it rests on.** The mutex, the semaphore and the bounded channel park a *computation*
rather than the carrier, and the two clauses of the acceptance are stated by the actors themselves: the
holders' `-enter`/`-exit` events carry exclusion and the unrelated `u` carries that a waiter does not
stall other work, and the exact accepted/rejected counts carry that the bound holds. On the revision
whose bodies are adapters over the stock shapes, the last two probes print `cancelLockAcquired = no` and
`cancelRecvValue = lost`: a release hands a permit to a waiter irrevocably, and a receive dequeues a
message into the task it returns, so a waiter the runtime then skips has already consumed it. A mechanism
whose wake is only a hint and whose waiter acquires in its own step prints `yes` and `present` here;
those two fields are the scenario's own outcome assertions on unfixed behaviour, and the rest of the
record holds either way. `syncbench|` is printed and never asserted.

______________________________________________________________________

### SC12 — blocking jobs run off the carrier, on a bounded pool, without stalling the executor

**Actor.** A Lean executable client of the runtime's blocking pool: four **blocking jobs** submitted through
the pool, each recording the thread it ran on, and a **heartbeat** computation whose every step is a carrier
step, so the executor has work to do while the jobs run. Nothing on the carrier blocks.

**Boundary.** `nix develop -c bash tests/executor-contract.sh SC12`, which invokes
`lake exe controls --runtime-blocking`. The check reads the one `block|` record the mode prints, and the mode's
own detached `blockctl|` detector control; nothing here calls a private function, reads a queue or a slot, or
inspects a thread table — the observation is the mode's record.

**Given.** A fresh executor (`Sched.Executor.new LeanIn.Task.Item 256 1`), a fresh `Runtime.Hooks.new`, a pool
`Runtime.BlockingPool.new 2`, four jobs, a twenty-five-millisecond `IO.sleep` each, a heartbeat of two hundred
cheap steps, and one stock task at `_root_.Task.Priority.default`. The carrier's tid is read on the mode's own
thread.

**When.** In one invocation the mode, inside one `Runtime.run`: spawns the four jobs, each
`Runtime.spawnBlocking pool hooks (jobBody i)` where `jobBody i` appends `job<i>-start`, records `IO.getTID`,
sleeps, and appends `job<i>-done`; spawns the heartbeat, whose every step appends `hb` and reads
`Runtime.pending hooks` into `pendingPeak`; submits one stock default-priority task and awaits it, recording
whether `stock` precedes the last `job<i>-done`; awaits every job, recording in each continuation the thread it
resumed on into `resumeTids`; awaits the heartbeat, then calls `Runtime.BlockingPool.shutdownAndWait pool`; and
returns. The returned unit is the synchronisation point — no clock enters any assertion — and the mode then
reads `Runtime.pending hooks` into `pendingAfter` and the pool's `exited` into `workersExited`.

**Then.** There is exactly one `block|` record, and its fields are exactly `jobs`, `carrier`, `jobTids`,
`poolWorkers`, `carrierDuringFirstJob`, `resumeTids`, `stockBeforeJobs`, `pendingPeak`, `pendingAfter`,
`workersExited` and `runUs`, in that order with nonempty values. `jobTids` and `resumeTids` are bracketed
comma-separated tid lists read with the fixture's existing bracket syntax, one tid per job in job order.

**The blocking jobs ran off the carrier:** every `jobTids` entry differs from `carrier`, and the shape cannot
be vacuous — `jobs ≥ 2` and `poolWorkers < jobs` with `poolWorkers ≥ 1`. It is a **bounded pool**, not a
thread per job: `distinct(jobTids) ≤ poolWorkers`, so four jobs shared at most two threads. `carrier` and
`jobTids` are read from the same record, so assertion 2 is not satisfied by a value appearing elsewhere in the
output, and `distinct` is computed rather than read. `carrierDuringFirstJob = yes` says the executor was **not
stalled** — the recorded event order carries a carrier `hb` step strictly between the first job's start and its
completion — and `resumeTids` all equal to `carrier` says every completion was delivered back on the carrier,
so nothing of ours ran on a job thread. `stockBeforeJobs = yes` says the stock pool was left untouched.
`pendingPeak = jobs` and `pendingAfter = 0` are the accounting: the runtime's outstanding-registration reader
saw every job while they were outstanding and none after the run returned and the pool was shut down, the first
being the affirmative control that makes the second a claim rather than an unbacked absence. `workersExited =
poolWorkers` says the pool's own shutdown drained and every worker exited. `runUs` is printed and never
asserted on.

The detector is exercised inside the same invocation: it accepts a well-formed record and rejects nine near
misses, among them `jobTids` all equal to `carrier` — the shape blocking jobs run to completion on the carrier
produce — four distinct `jobTids`, `carrierDuringFirstJob=no`, a completion resumed off the carrier,
`stockBeforeJobs=no`, `pendingPeak=0`, `pendingAfter=1`, a worker short of `poolWorkers`, and a record with
nothing to observe. Every near miss is built from the record syntax and the expectation, never from the mode's
output, and a control that does not hold is a fixture defect rather than this `Then`. The mode's own
`blockctl|` readings must also hold: the distinct-thread detector counts two on two distinct tids and one on a
repeat, the order detector rejects the blocking-shaped order `job0-start,job0-done,hb` and accepts the
interleaved `job0-start,hb,job0-done`, and the stock guard rejects a record that says the stock pool was taken.
The `Then` must hold in each of the mode's three invocations.

**Why, and what it rests on.** The executor has one carrier, so `IO.sleep` — and every synchronous leaf — blocks
it. The pool moves that work to dedicated threads (`Task.Priority.dedicated` is above `Task.Priority.max`),
bounded by the caller's width rather than one thread per job, and assertion 2 is the off-carrier claim itself
while `carrierDuringFirstJob` and `pendingPeak` read the same defect from the executor's and the registry's
side. The order reading is the actors' own annotation order rather than elapsed time, which is why the scenario
can state that a carrier step fell inside the first job's start→completion without reading a clock: on the
unfixed route the job is one carrier step, so its start and completion are adjacent in the log.

______________________________________________________________________

### SC11 — a disconnect cancels the work, and no step of it runs afterwards

**Actor.** A Lean executable server, one process, three actors on one executor: a **work** computation that counts
once and then parks on a leaf it does not own; the **watcher**, which is the run's own computation — it accepts the
first connection, waits for the peer to leave, and in that same step reads the counter and cancels the work; and a
**second connection**, which the client opens after the cancellation and which is echoed.

**Boundary.** `nix develop -c bash tests/executor-contract.sh SC11`, which invokes
`lake exe controls --runtime-cancel`. The cancellation is a public operation on a handle, and the check reads the
one `cancel|` record and nothing else.

**Given.** A fresh executor, a listener bound to `127.0.0.1:0`, a work computation spawned before the watcher's
first step, a leaf the work parks on that the watcher resolves *after* it cancels, and a second leaf that is never
resolved.

**When.** The client connects and closes. The watcher's read on that connection reports end of stream — the
disconnect — and in the same step it reads the counter into `counterAtCancel` and requests the cancellation, then
resolves the first leaf. That leaf's completion resumes the work's step, which is exactly the step the cancellation
is meant to stop. A second client then connects, sends, and reads its echo. The run returns, and the counter is read
again into `counterFinal`.

**Then.** There is exactly one `cancel|` record, and its fields are exactly `disconnect`, `second`,
`counterAtCancel`, `counterFinal`, `pendingAtCancel`, `pendingAfterCancel`, `cancelled`, `doubleCancel` and
`runUs`, in that order with nonempty values.

`counterAtCancel = counterFinal` is the assertion: **no step of a cancelled computation runs after the cancellation
was requested.** It is the abort law rather than a timing claim — the counter is read inside the cancelling step and
again after the run returns, so no clock enters it, and because the leaf is resolved after the cancellation, the
resumed step is one that would otherwise have run. `counterAtCancel ≥ 1` forbids the vacuous reading: a run in which
the work had not started would satisfy the equality with `0 = 0` and prove nothing. `pendingAtCancel = 1` says a
registration of the work really was outstanding when the cancellation arrived; `pendingAfterCancel = 0` says it is no
longer counted as work in flight. `cancelled = canceled` is the handle's awaiter waking with the cancellation rather
than parking for a value that will never come, and `doubleCancel = ok` is the first-writer law holding when a second
cancellation arrives. `second = yes` folds in W5's second clause: a connection served *after* a cancellation is
unaffected by it. `runUs` is printed and never asserted on.

The detector is exercised inside the same invocation: it accepts a well-formed record and rejects nine near-miss
records, among them `counterFinal` one past `counterAtCancel` — the shape production prints while nothing consults
the token — and `pendingAfterCancel=1`. Every near miss is built from the record syntax and the expectation, never
from the mode's output, and a control that does not hold is a fixture defect rather than this `Then`.

**Why, and what it rests on.** Cancellation here is *ours*, because Lean offers no other stopping power. The
runtime's own documentation is explicit that a task created by `IO.bindTask` "will run even if the last reference to
the task is dropped" (`Init/System/IO.lean:266-269`), and a search of the whole `Std` tree finds `IO.cancel` and
`IO.checkCanceled` in one test helper and nowhere a socket or timer would observe them. A leaf therefore cannot be
cancelled, and the gate is placed where a step is run: a step whose token is set does not execute, whether it was
enqueued before the cancellation or after it.

The two counted operands are read about *this* computation's registrations rather than about the runtime's, because
the runtime's total includes the cancelling computation's own and is not stable at the moment of a read — a
cancelling step is itself a resumed continuation, and whether its registration is already marked finished is another
thread's business. `pendingAtCancel` is the work's own registration, outstanding because the work is parked on the
leaf the watcher has not resolved yet. `pendingAfterCancel` is the same count read *in the cancelling step,
immediately after the cancellation*: it is `0` because the cancellation retired the entry, which is what makes that
reading the one that discriminates the retirement half. The gate's half is what the counter is for — with the gate
missing, the resumed step runs and the counter advances.

______

### SC10 — a stop drains: the connection in flight completes, and nothing is left outstanding

**Actor.** A Lean executable server that accepts one connection and echoes it, with the connection itself stopping
the executor from inside the body being served. The client is `Std.Async`'s: it connects, sends, reads its echo
and closes.

**Boundary.** `nix develop -c bash tests/executor-contract.sh SC10`, which invokes
`lake exe controls --runtime-drain`. The stop is a public executor operation; the check reads what the run recorded
and the two counts it read back afterwards.

**Given.** A fresh executor, a listener bound to `127.0.0.1:0`, and a 9-byte payload.

**When.** In one invocation the server's accept loop polls, accepts the connection, and the body — before echoing —
stops the executor. The loop notices on its next poll, stops accepting, and waits for the connection it already
has. The client reads its echo and closes, which ends the connection; the drain then returns, and the run returns
the loop's own value.

**Then.** There is exactly one `drain|` record, and its fields are exactly `served`, `echoed`, `inFlightAfter`,
`pendingHooks`, `listener` and `drainUs` in that order with nonempty values.

`served` is `1` and `echoed` is `yes`: the connection that was in flight when the stop arrived **completed** — its
echo came back to the client — which is what "a stop drains" means and what W5's acceptance asks for.
`inFlightAfter` is `0`: the pool holds nothing once the run returns. And `pendingHooks` is `0`: **no leaf
registration is left outstanding.** That last field is the one no model of pool items could state, because a task
parked on a leaf holds no pool item at all — a driver that stopped there would abandon the continuation without
disturbing any counter, which is exactly the bug this scenario was written to catch.

The detector reading those four conditions is exercised inside the same invocation: it accepts a well-formed
record and rejects four near misses — a connection dropped by the stop (`echoed=no`), a pool still holding work, a
registration left outstanding, and a run that served nothing. Every near miss is built from the record syntax and
the expectation, never from the executable's output, and a control that does not hold is a fixture defect rather
than this `Then`.

**Why, and what it cost.** Two bugs came out of writing it, both in the driver rather than in the sockets.

*The stop abandoned instead of draining.* `Runtime.blockOn` ended the driver as soon as the pool was empty and the
executor was stopping — but a stopped executor still holds work as continuations registered on leaves, which are
not in the pool by construction. So `Runtime.run` threw "the driver stopped before the computation finished", the
connection's continuation was never resumed, and a client waiting on it hung in `recv`. The model's shutdown says
*drain*; the driver aborted, and running it is what showed the difference.

*Then the wait was not a wait.* The fix had `blockOn` park directly, without recording that it was parking — and
`submit`/`spawnBase` notify **only when `parked ≠ 0`**. So the driver slept with the loop's poll timer pending, the
timer completed and enqueued the loop's continuation, and nothing told the driver. It now sets `parked` before
waiting and clears it on waking, the way `Executor.work`'s predicate does. That is the protocol, and skipping it
was invisible until a scenario had work in flight when the stop arrived — which is why this is a scenario and not a
diagnostic.

The first version of the mode also died with `104 connection reset by peer`, for the reason SC9 records: a socket's
descriptor dies with the last use of the object owning it, and the loop's final `tryAccept` is not the end of the
run. The listener is read again after the drain for that reason.

______

### SC9 — a failed socket operation arrives as a value, and the listener must outlive its last use

**Actor.** A Lean executable client that connects twice: once to a port nothing listens on, and once to a
listener the same program holds. The second is the affirmative control for the first.

**Boundary.** `nix develop -c bash tests/executor-contract.sh SC9`, which invokes
`lake exe controls --runtime-connect`. Nothing is accepted in this mode — the point is the connect, not a
conversation — so the check reads the two outcomes and the listener's own address and nothing else.

**Given.** A fresh executor, a listener bound to `127.0.0.1:0`, and two `connect`s through the runtime's own
wrapper, which returns failures as values.

**When.** In one invocation the client connects to port 1, which nothing user-level can be listening on, and then
to the listener's address, which it reads in the same step. It prints the refusal text, the second outcome, and
the listener's address read again afterwards.

**Then.** There is exactly one `connect|` record, and its fields are exactly `refused`, `accepted` and `listener`
in that order with nonempty values.

`refused` is the *refusal* — its text carries `error code: 111`, and it arrived as a value, so the run reached
its own record rather than dying. `accepted` is `ok`: a connect to a live listener succeeds, which is what makes
the refusal a reading rather than a reader that reports failure for everything. And `listener` is non-empty,
because the socket had to still exist at the end for either of the first two to mean anything.

The detector reading those three conditions is exercised inside the same invocation: it accepts a well-formed
record and rejects three near misses — an accepted connect that also failed, a refusal reported as success, and a
listener that did not survive the run. Every near miss is built from the record syntax and the expectation,
never from the executable's output, and a control that does not hold is a fixture defect rather than this `Then`.

**Why, and what it cost to learn.** `interface.md` §5 records that our `Async` has no error channel; `EAsync` is
that channel, and this is the first scenario that reads it — a socket failure has to be an ordinary value,
because a client closing a connection mid-request is the normal case for a server.

The scenario also carries a rule that only showed up by writing it. **A socket's descriptor dies with the last
*use* of the Lean object that owns it, not at the end of its scope.** The first version read the listener's
address immediately before connecting and the listener was collected in between, so the connect was reset by a
socket that had just served sixteen connections; two of four runs died with SIGSEGV instead, which is the same
hazard winning a different race. Keeping the listener in a reference whose own last use falls *after* the connect
holds both alive through it, and six consecutive runs then read `refused=…111`, `accepted=ok` and a bound
listener. That is a rule the driver obeys for its listener and for every connection it serves, and it is here
rather than in the driver because this is the smallest place it can be seen.

______________________________________________________________________

### SC8 — timers on our carriers: sleeps that park rather than occupy, and timeouts that fire

**Actor.** A Lean executable client of LeanIn's timer leaf and its timeout combinator: `16` sleepers of 50 ms
each as steps of one executor driven by one thread, a task spawned while all of them are pending, and two
`withTimeout` calls whose inner computations are chosen so that the outcome is not a matter of timing.

**Boundary.** `nix develop -c bash tests/executor-contract.sh SC8`, which invokes
`lake exe controls --runtime-time`. The sleeps and the timeouts are the public operations; the check reads the
event order the client recorded where the events happened, plus the two outcome values, and nothing else.

**Given.** A fresh executor, `16` sleepers on a 50 ms timer, one extra task spawned after them, one inner
computation that never finishes, and one that finishes immediately.

**When.** In one invocation the client spawns the sleepers, spawns the late task, awaits all of them, and then
runs the two timeouts. Each sleeper records `start:i` before it sleeps and `wake:i` after; the late task records
that it ran.

**Then.** There is exactly one `time|` record, and its fields are exactly `sleepers`, `overlap`,
`lateBeforeWake`, `wakes`, `timeoutHit`, `timeoutMiss`, `firstWins`, `lateTimerIgnored` and `sleepUs` in that
order with nonempty values.

`overlap` is `true`, and it is the whole point: **every one of the `16` starts precedes the first wake**, so the
sleeps parked on the timer rather than occupying the carrier. That is the clock-free form of "they finish in
about `d`, not `N × d`" — an implementation that slept on the carrier would wake the first sleeper between the
first two starts, and this reading would be `false`. `lateBeforeWake` is `true`: the task spawned while every
sleeper was pending ran before the first wake, which is the same fact seen from the other side. `wakes` equals
`sleepers`, so every sleeper did wake, and `timeoutHit` is `none` while `timeoutMiss` is `some:7` — the inner
computation that never finishes times out, the one that finishes immediately does not, and neither outcome
depends on how long a run takes.

`firstWins` and `lateTimerIgnored` are the task layer's first-writer law, which is the only thing W3 added to
it, and they are recorded rather than left to the timeout cases above. `firstWins` is `some:1`: two writes to one
cell were issued **in order** — not raced, because which of two racing writers wins is a scheduling fact and
this is a claim about the operation — and the value that arrives is the first, with the second ignored.
`lateTimerIgnored` is `some:7`: a `withTimeout` whose computation finished immediately, followed by a 40 ms sleep
against a 5 ms deadline, so the timer *does* fire — inside the run, after the winner wrote — and the value is
still the computation's. The reachable defect is exact: the loud `Join.resolve` in either position would raise
out of the driver instead, so reaching the record at all is part of the evidence, and the near misses for this
detector are a first value that was overwritten and a late timer that overwrote the winner.

`sleepUs` is printed and never asserted, for the reason SC7 gives.

The detector reading those seven conditions is exercised inside the same invocation: it accepts a well-formed
record and rejects seven near misses — `overlap=false`, `lateBeforeWake=false`, `wakes` one short, each timeout
outcome swapped, `timeoutMiss=none`, a `firstWins` of `some:2` where the second writer overwrote the first, and a
`lateTimerIgnored` of `none` where the timer overwrote the winner. Every near miss is built from the record syntax and the expectation,
never from the executable's output, and a control that does not hold is a fixture defect rather than this
`Then`. The executable's own two controls are read from its `timectl|` record and required to hold: its overlap
detector reads `false` on a deliberately blocking-shaped order (`start,wake,start,wake`), and its wake counter
reads one fewer than `sleepers` when a wake is removed — the second derived from the record's own `sleepers`
field rather than retyped.

**Why.** A timer is the leaf a service leans on for every deadline it has, and the claim being checked is not
that a clock advanced but *where the waiting happened*: on libuv's loop, with the carrier free. Reading that
from the recorded order rather than from elapsed time is what makes the check survive a loaded machine — and it
is why the one block that does measure is printed rather than asserted, and why the first version of this
detector, which demanded that everything before the first wake be a start, was caught by its own control rather
than by the `Then`.

______________________________________________________________________

### SC7 — sockets on our carriers: one server thread, and a client that is not on it

**Actor.** A Lean executable server that binds a loopback socket, accepts `16` connections through an accept
loop of its own, and echoes each one until the peer stops — all as steps of one executor driven by one thread —
with a client that is deliberately **not** ours: `Std.Async`'s TCP client, driven by `Async.block` on the
calling thread.

**Boundary.** `nix develop -c bash tests/executor-contract.sh SC7`, which invokes
`lake exe controls --runtime-net`. The client connects over a real socket, and the server reads and writes
through the public socket operations only; nothing in the check reaches into a queue, a slot or a thread table.

**Given.** A fresh executor, a listener bound to `127.0.0.1:0` — the OS chooses the port and the client is told
what it chose — `16` concurrent client connections, and a 20-byte payload each connection sends and expects
back byte for byte.

**When.** In one invocation the server accepts and serves, and the client connects, sends, reads and shuts
down; every connection task records the thread it started on. The executor's observer is read twice: before the
driver starts, with three no-op items deliberately queued, and again after the driver returns.

**Then.** There is exactly one `net|` record, and its fields are exactly `connections`, `serverThreads`,
`clientAmongServer`, `echoes`, `heldBefore`, `inFlightAfter` and `wallUs` in that order with nonempty values.

`serverThreads` is `1`: the accept loop and all sixteen connection tasks ran on one thread — the single-carrier
claim, measured where the work happened rather than inferred from the configuration. `clientAmongServer` is
`false`: that thread is not the client's, so the client's driver is genuinely a second thread in the picture,
and what is asserted is where *our* work ran rather than that only one thread existed. `echoes` equals
`connections`: every reply was byte-identical to its request, so the loop read and wrote rather than closing on
an empty read. `inFlightAfter` is `0`: nothing is left held once every connection has been awaited. And
`heldBefore` is non-zero — the affirmative control for that last reading, since the observer is the same one on
both sides and a reader that cannot see work would report zero either way. A first attempt at this control read
the observer from inside a running connection body and got `0`, which is why it now stages the queue instead: a
carrier drains the pool as it goes, so a reading taken while one is running is legitimately empty.

The detector reading those five conditions is exercised inside the same invocation. It accepts a well-formed
record and rejects four near misses — `serverThreads=2`, `clientAmongServer=true`, `echoes` one short of
`connections`, and `inFlightAfter=1` — each built from the record syntax and the expectation, never from the
executable's output, with a control that does not hold reported as a fixture defect rather than as this `Then`.
The executable's own two detector controls are read from its `netctl|` record and required to hold: the
distinct-thread detector counts two on a two-distinct sample and one on a repeat, and the reply comparison finds
nothing against a payload with one extra byte — so neither detector is stuck at the value the `Then` wants.

**Why.** W10's survey found that the shipped server's accept loop is a stock `Task`, which cannot be moved onto
our carriers, so a server that runs here owns its loop; that loop's only interesting claim is *where* it runs,
and a thread identity is the only way to check it from outside. The echo is what keeps the claim honest — a
runtime that closed each connection before reading it, or that accepted on one thread and served on another,
could still report a plausible connection count. `wallUs` is printed and never asserted: it moved by a factor
of two between runs of the same invocation, which is why this check reads identities and counts and not clocks.

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
