# Bridge contract scenarios

Behaviour checks for the bridge contracts in `LeanIn/Theory/Bridge.lean`, driven at the public boundary —
the `Std` primitives — and checked against records the carriers themselves emit.

```
nix develop -c bash tests/bridge-contract.sh BT1     # or BT2, BT3
```

Records come from `lake exe bridgecontrols`, the public executable for bridge observations. Running that
with no argument runs every trace in sequence. Each scenario's checker is exercised in the same invocation
against mutations of the records that same execution produced.

## What a trace test can and cannot do

It can **falsify** a contract: if the runtime produces an order the contract forbids, the contract is wrong.
It cannot **establish adequacy** — that the contracts are all of what the runtime does — and no number of
passing runs gets there. Adequacy is the execution-semantics obligation, and it is not this.

A trap worth naming, because the records here are written by the carriers rather than read out of the
runtime: `Std.BaseMutex` and `Std.Condvar` have no observation hooks, so *the program's own annotations are
the trace*. That is enough for ordering and ownership claims, which is what the scenarios state. It is not a
runtime trace and cannot see anything the carrier does not name.

The checker addresses records **by field, never by line order** — a concurrent trace has no line order, so
a mutation that only moved lines would be accepted, and rightly. The mutations therefore change a field.

## BT1 — the wait cycle, on the narrow path

*From the reference handoff: "Start with one narrow path—such as lock, predicate check, wait and unlock".*

| | |
|---|---|
| **Actors** | a caller carrier, and a sibling on its own dedicated native carrier |
| **Boundary** | `Std.BaseMutex.{lock,unlock}`, `Std.Condvar.{waitUntil,notifyAll}` |

The caller acquires, checks the predicate, and waits; the sibling acquires the lock the caller released
inside the wait, opens the predicate, notifies, releases.

| Relation | The claim it presses |
|---|---|
| `parking < sibling.acquired` | `wait` really releases the lock — the sibling could not take it otherwise |
| `sibling.acquired < resumed` | the release is *inside* the call, not before it |
| `notified < resumed` | de-enrolment came from the notification, not a spurious wake |
| `resumed` holds `yes`, `resumed < released` | the caller holds the lock again on return |
| exactly one record per stage | no stage ran twice, none missing |

## BT2 — no notification outlives its episode

*The reference handoff's "notified episode followed by a fresh wait".* Two park/resume episodes, and the
question is whether the first episode's notification can release the second wait.

| Relation | The claim it presses |
|---|---|
| each `parked < its notified` | a notification is delivered to a wait that has started, not one about to |
| each `notified < its resumed` | the resume follows its own notification |
| `stage 1 resumed < stage 2 parked` | the episodes are sequential, not overlapping |

**One waker looping over both episodes is unsound, and it failed intermittently here.** After its first
notification the caller is *waking*, both it and the waker race for the mutex, and if the waker wins it
spends the second notification on a caller that has not parked again — the second wait then parks with no
waker left. Two earlier designs hung for this reason, one of them 2 runs in 3. The fix is one waker per
episode, started **while the lock is held**: it cannot reach its `lock` until this carrier is parked in its
own episode, so every episode happens and every notification reaches the wait it was meant for. A scenario
whose synchronization depends on which thread wins a race is not a scenario.

## BT3 — two live objects are two objects

*The reference handoff's "duplicate runtime-object mapping".* Another carrier tries both mutexes while this
one holds only `a`.

| Relation | The claim it presses |
|---|---|
| `trylock-a` → `refused` | the held object is not available, and with no blocking |
| `trylock-b` → `granted` | the free one *is* — the affirmative control, in the same run |
| both inside `lock-a < … < unlock-a` | so both were observed against the same live pair |

The refused attempt is the negative and the granted one is its control, which is what an absence claim
needs: a detector that can only ever say "refused" would prove nothing. Both are `tryLock`, so the refused
one cannot block, and both come from a carrier that does not own `a` — `try_lock` on one's own mutex is
undefined behaviour, which is what the A2 control exists to avoid.

## The checker's own controls

Each scenario accepts the real trace and rejects six near-misses built from its own records:

| Mutation | Rejected because |
|---|---|
| two `ns` values swapped so a stated order is violated | the ordering relation *is* the claim |
| the same, for the relation that names the contract's subject | as above |
| a stage's record removed | a missing stage is not a passing trace |
| a record duplicated | a stage that ran twice is not the cycle |
| a field appended | the record shape is part of the contract |
| two fields transposed | so is their order |

BT3's is a *value* swap rather than an `ns` swap: exchanging `granted` and `refused` between the two
attempts is the countermodel itself — the held object appearing available.

A swap whose pattern matches no record, or a mutation identical to the real trace, is reported as a failure
rather than counted as a pass. Both guards exist because a silent no-op mutation looks exactly like a
working control.

## Pinned for the audit

Every run prints the toolchain and platform it observed, because a falsification is only meaningful against
the revisions that produced it.
