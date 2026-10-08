# Bridge contract scenarios

Behaviour checks for the bridge contracts in `LeanIn/Theory/Bridge.lean`, driven at the public boundary —
the `Std` primitives — and checked against records the carriers themselves emit.

Run one with:

    nix develop -c bash tests/bridge-contract.sh BT1

The checker is `tests/bridge-contract.sh`; the records come from `lake exe bridgecontrols`, the public
executable for bridge observations.

## What a trace test can and cannot do

It can **falsify** a contract: if the runtime produces an order the contract forbids, the contract is
wrong. It cannot **establish adequacy** — that the contracts are all of what the runtime does — and no
amount of passing runs gets there. Adequacy is the execution-semantics obligation, and it is not this.

A trap worth naming, because the records here are written by the carriers rather than read out of the
runtime: `Std.BaseMutex` and `Std.Condvar` have no observation hooks, so *the program's own annotations
are the trace*. That is enough for ordering and ownership claims, which is what the scenarios state. It is
not a runtime trace and cannot see anything the carrier does not name.

## BT1 — the wait cycle, on the narrow path

*From the reference handoff: "Start with one narrow path—such as lock, predicate check, wait and unlock".*

| | |
|---|---|
| **Actors** | a caller carrier, and a sibling on its own dedicated native carrier |
| **Boundary** | `Std.BaseMutex.{lock,unlock}`, `Std.Condvar.{waitUntil,notifyAll}` |
| **Observable outcome** | the order of the carriers' own records, bound to their named fields |

The caller acquires, checks the predicate, and waits; the sibling acquires the lock the caller released
inside the wait, opens the predicate, notifies, releases. Each records `ns` from `IO.monoNanosNow`, so the
ordering claims are stated over a field rather than over output order.

### The relations, and which contract each one presses

| Relation | The claim it tests |
|---|---|
| `caller.parking < sibling.acquired` | `wait` really releases the lock — the sibling could not acquire otherwise (`afterWait_releases`, `wait_spec`) |
| `sibling.acquired < caller.resumed` | the caller is still parked when the sibling holds the lock — the release is inside the call, not before it |
| `sibling.notified < caller.resumed` | the de-enrolment came from the notification, not from a spurious wake (`wait_spec`'s second conjunct) |
| `caller.resumed` holds `yes` | the caller holds the lock again on return (`wait_spec`'s first conjunct) |
| `caller.resumed < caller.released` | it re-acquired before releasing |
| exactly one record per stage | no stage happened twice, and none is missing |

The mutex is what makes these hold rather than merely likely: the caller holds it while it reads the
predicate and releases it only inside the wait, so the sibling cannot open the predicate in the gap, and
the caller cannot leave the wait before the predicate is open. A spurious wake returns the caller to the
wait, so the notification relation survives one.

### The checker's own controls

The detector is exercised in the same run, on records captured from the same execution:

| Mutation of the real record set | Must be rejected because |
|---|---|
| two `ns` values swapped so the park window is violated | the ordering relation is what is being claimed |
| `sibling.notified` moved after `caller.resumed` | the de-enrolment relation is not output order |
| the `sibling.acquired` record removed | a missing stage is not a passing trace |
| a record duplicated | a stage that ran twice is not the cycle |
| a field appended to a record | the record shape is part of the contract |
| two fields transposed | so is their order |

An acceptance on the real set on its own would prove nothing; the pair is the point.

## Pinned for the audit

Every run prints the toolchain and platform it observed, because a falsification is only meaningful
against the revisions that produced it.
