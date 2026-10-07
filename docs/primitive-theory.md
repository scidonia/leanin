# A theory of the primitives

What the externs `leanin` stands on actually guarantee, stated precisely enough to be used as
hypotheses. This is the piece that closes the semantics gap: without it there is no term for a
theorem to be *about*.

---

## 1. What a theory has to be

Not a pile of axioms in the void. The shape is an **interpretation**:

- an abstract machine `M` — a state type and a transition relation, ordinary Lean;
- an interpretation `⟦·⟧` from the fragment of Lean `IO` we use into `M`'s transitions;
- one axiom per primitive, of the form "`⟦op⟧` is *this* transition relation".

Then every theorem is about `M`, stated in plain Lean, and the trusted base is the claim
"the C++ behaves as `⟦·⟧` says".

This is not smuggled assumption. `BaseMutex.lock`, `Condvar.wait` and the rest are `opaque` with
`@[extern]` (`Mutex.lean:28,38,51,96,100,104`) — they are **genuinely uninterpreted constants**. Giving
them a meaning is a precondition for proving anything at all, not an extra leap. The leap is the one
already stated: that the implementation matches the interpretation.

**Why not Iris or `Std.WP`.** Both reason about a *modelled language*, and our code is Lean `IO`.
Either choice forces us to model our own code *and* still bridge to Lean — two gaps instead of one.
What our code actually needs is far less: every critical section is a transaction, and mutual
exclusion gives serializability (§5).

---

## 2. The machine

`M` is deliberately small, and it is sized to the code we actually write:

| Component | Kind | Why it is there |
|---|---|---|
| `engine` | Lean data | the run queue, the inject queue, per-task bookkeeping, the stopping flag |
| `locks : LockId → LockState` | abstract | one per `Mutex` |
| `condvars : CondvarId → set ThreadId` | abstract | waiters only — **no payload** (A5) |
| `threads` | set | holders and waiters |
| `clock : Nat` | monotone | `monoNanosNow` |

A **step** is one of: a local engine transition (pure, no axiom needed); a lock operation; a condvar
operation; or — in v2 — a spawn.

The point of this shape: *the engine is Lean data*, so anything the scheduler computes is sequential
Lean reasoning. The axioms exist only at the four boundaries where the engine touches a primitive.

---

## 3. The axioms

`needed` says which milestone consumes it: **v1** = single-carrier core (D2), **v2** = multi-carrier.

| # | Primitive | Guarantee | `needed` |
|---|---|---|---|
| A1 | `BaseMutex.lock` / `unlock` | mutual exclusion; release *synchronizes-with* the next acquire, so a holder observes every write of the previous holder | v1, v2 |
| A2 | `BaseMutex.tryLock` | non-blocking; returns `true` iff it acquired | v1 |
| A3 | `BaseMutex.unlock` | requires ownership; releasing without holding is undefined | v1, v2 |
| A4 | `Condvar.wait` | **atomically** releases the mutex and blocks; reacquires before returning | v1, v2 |
| A5 | `Condvar.notifyOne` / `notifyAll` | unblocks ≥1 / all *current* waiters | v1, v2 |
| A6 | dedicated task ⇒ `pthread_create` | a new OS thread runs the closure; creation *happens-before* its first instruction; joinable | **v2 only** |
| A7 | `IO.monoNanosNow` | non-decreasing | v1 |

Sources: A1–A3 `mutex.cpp:27–39` → `std::mutex`, ISO C++ `[thread.mutex.requirements]`; A4–A5
`mutex.cpp:55–69` → `std::condition_variable`, `[thread.condition.condvar]`; A6 `object.cpp:792` →
`thread.cpp:120–137`; A7 `object.cpp:421`.

### Which of these turned out to be theorems

Building the model (`LeanIn/Theory/World.lean`) changed the accounting, and for the better. A1's mutual
exclusion, A3's precondition impossibility, A4's permission for spurious wakeups, and A5's absence of
memory are all **proved as theorems about the model** — none of them is assumed. `#print axioms`
confirms it, so the claim is mechanical rather than a promise:

```
'LeanIn.notifyOne_no_waiters' depends on axioms: [propext]
'LeanIn.reacquisition_while_others_wait' depends on axioms: [propext, Quot.sound]
```

Lean's built-in axioms only — no bridge axioms. What remains axiomatic is the connection between the
model and the running program (`LeanIn/Theory/Bridge.lean`, seven axioms), each citing the C++ or the
standard clause it claims the runtime honours. **The TCB is therefore smaller than this document
originally claimed**, and the audit is a build step rather than an intention.

### The absences

These are the load-bearing half, because each one *forces* a design constraint rather than being a
caveat we note and move past.

**A1 — no fairness, no order.** `std::mutex` is explicitly unspecified-order. So: no
starvation-freedom, no FIFO *across threads*, no bounded acquisition latency. Our own FIFO discipline
governs **queue order, not dispatch order**, and the docs must not conflate them. This is exactly
mCertiKOS's position — their lock starvation-freedom holds only under an explicit fairness assumption
on the hardware/OS scheduler.

**A4 — spurious wakeups are permitted.** A bare `wait` is not a condition. Therefore
`Condvar.waitUntil` / `Mutex.atomicallyOnce` (`Mutex.lean:107,164`) is the *only* admissible shape,
and a bare `wait` should be unrepresentable in `leanin`'s API.

**A5 — notifications are not queued.** A condvar has no memory: `notify` with no waiter is lost, and
notifying outside the lock can lose the wakeup. So every park/wake protocol carries its own state —
the `stopping`/`jobs` flags are *forced*, not defensive. Park/unpark correctness is a protocol
obligation we discharge, never something a primitive gives us.

**A6 — no scheduling guarantee.** Spawn says a thread exists and what happens-before it; nothing about
when it runs, on which core, or in what order relative to its siblings. Any *progress* claim in v2
therefore needs either a fairness assumption or a proof obligation about our own protocol plus that
assumption.

**A7 — no resolution guarantee.** A clock is not a scheduler; it cannot bound latency.

---

## 4. What the axioms are consumed by

Exactly one place: a **serializability lemma**.

> If the interpretation of each critical section is a transaction on the guarded state, and A1–A3
> hold, then every observable behaviour of the concurrent program is the behaviour of *some*
> sequential execution of those transactions.

Once that is proved, all scheduler correctness is **sequential reasoning about transactions** — which
is why the axioms stay out of the way instead of threading through every proof. Concretely:

- the abstract invariant is over `engine` state, untouched by concurrency;
- each critical section is one transaction, proved to preserve it;
- A4/A5 appear only in the park/wake protocol, whose obligation is "no lost wakeup", stated against
  the condvar's waiter set and discharged by the protocol's shape (state checked and notification
  issued under the same lock).

**Derived, not decreed.** Two property-ladder consequences fall out of the axioms rather than being
editorial choices:

- **P2 (completion)** must be stated *conditional on a fairness hypothesis* about the OS/thread
  layer, because A1 gives no fairness and A6 gives no scheduling guarantee. The hypothesis belongs in
  the theorem statement.
- **P9 (fairness)** is not attainable from these primitives at all. It can only be a property of our
  own discipline under that hypothesis.

---

## 5. Discharge

An axiom nobody checks is a liability, so each is discharged three ways.

**1. The model is published.** A1–A5 are the ISO C++ specifications of `std::mutex` and
`std::condition_variable`; A6 is POSIX `pthread_create`. The axiom cites a clause, not our optimism.

**2. The wrapper adds nothing.** `mutex.cpp` is 158 lines of boxing and `static_cast` — there is no
caching, no bookkeeping, no state. `lean_io_basemutex_lock` is literally `get(mtx)->lock()`
(`:27–29`); `lean_io_condvar_wait` is `std::condition_variable::wait` under `adopt_lock_t` (`:55–60`).
So "the wrapper preserves the spec" is a *reading*, not a leap. `thread.cpp:120` is `pthread_create`
with a 1 GiB reserved stack.

**3. A control per axiom** — a test that would fail if the axiom were false, because a marker that
never fires passes forever:

| Axiom | Control |
|---|---|
| A1 | an unguarded shared counter loses updates under contention; the same counter under a `Mutex` does not. Shows mutual exclusion is doing work. |
| A2 | `tryLock` returns `false` exactly while another thread holds the lock, and never blocks. |
| A4 | a bare `wait` without a predicate returns even though nobody notified — demonstrating why `waitUntil` is mandatory. |
| A5 | `notify` with no waiter, then `wait`, blocks: the notification is lost. Then the same shape with state+lock held does not. |
| A6 | writes before spawn are visible in the thread (happens-before), and the thread is joinable. |
| A7 | `monoNanosNow` is non-decreasing across samples in several threads. |

---

## 6. What is deliberately *not* in the theory

- **Atomics.** Not exposed by Lean (grepped `Std.Sync`, `Init/System`: no load/store/CAS). Lock-per-queue
  (D4) means v1 does not need them; adding them later means adding a primitive *and* weak-memory
  reasoning, which is a separate decision.
- **`IO.Promise`.** Mutex+Condvar covers everything we need, so it stays out of the TCB. Anything not
  on the list is not used (D7).
- **`IO.Ref`.** Open as O1 in [`decisions.md`](decisions.md); the leaning is to keep it invisible
  behind `Mutex α` so that reasoning outside a lock is unrepresentable.
- **Fairness and real time.** Not provable from A1–A7 and not claimed. See §3 absences.
- **The compiler and FFI.** Lean's code generator, the C++ compiler, and the ABI are trusted and
  unmodelled. They are part of the TCB and belong in the same table as the axioms, not in a footnote.
