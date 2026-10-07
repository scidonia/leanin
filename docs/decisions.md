# Decisions

Settled decisions and the evidence each rests on. Evidence anchors are in
[`lean-scheduler.md`](lean-scheduler.md) (the current runtime), [`tokio-map.md`](tokio-map.md) (what
we are taking) and [`evidence.md`](evidence.md) (measurements). Two decisions are still open; they are
at the bottom and nothing downstream should be treated as fixed until they close.

---

## Settled

### D0 — No toolchain fork. Extern primitives, policy in Lean.

`leanin` is a separate library; the toolchain is not patched. The scheduling *policy* is Lean code;
only a closed list of primitives is extern.

**Why not patch.** The scheduler is a global singleton — `static task_manager * g_task_manager`
(`object.cpp:1095`), constructed at startup, with no handle, no second instance, and no injection
point. A patch means owning a Lean fork indefinitely, and it puts our code inside the C++ file we are
trying to get out of.

**Why this is viable at all.** The primitives we need already exist and are honest pass-throughs:
`Std.Sync` gives `BaseMutex` and `Condvar` (→ `std::mutex`, `std::condition_variable`), and
`Task.Priority.dedicated` yields a real `pthread` per task (`object.cpp:792` → `thread.cpp:120`).

**Consequence.** The TCB changes shape: from "the C++ task manager" to an enumerated primitive list
(see D7 and [`primitive-theory.md`](primitive-theory.md)).

### D1 — Provability first; performance measured, not targeted.

Machine-checked properties are the deliverable. Benchmarks are regression guards and honesty checks,
not success criteria. Where a faster design is less provable, the provable one wins and the
difference gets measured and stated.

### D2 — Single-carrier first. The M:N scheduler is a refinement, not the first build.

v1 is a single-carrier (`current_thread`-shaped, `LocalRuntime`-shaped) executor driven on the
caller's thread.

**Why.** The scheduler's own logic becomes a sequential program over a queue — the run queue in
Tokio's `current_thread` is a plain `VecDeque` (`scheduler/current_thread/mod.rs:65`) and the loop at
`:823–880` is ordinary sequential code. That core is provable with plain invariants and needs none of
the mutex axioms. Cooperative task interleaving is a sequential notion, so fairness and liveness
become properties of *our* queue discipline rather than of the OS.

**The three things it buys.** A sequential, provable core; a deterministic runtime as the *same*
artifact (one nondeterministic input: the inject queue); and no thread-creation axiom in v1.

**What it costs, stated plainly.** No parallelism. And it does **not** fix the 801 ms blocking
pathology — with one carrier a blocking task blocks everything, so the blocking pool is *forced*
early rather than deferred.

**Shape it on `LocalRuntime`, not `current_thread`.** `current_thread`'s core is an
`AtomicCell<Core>` that another thread can claim and drive (`:210`, `:921`). `LocalRuntime` is
internally the same scheduler but `!Send`/`!Sync` (`runtime/local_runtime/runtime.rs:38`), removing
core migration — a case not worth proving — and giving `LocalSet`-style non-`Send` tasks for free.

### D3 — Own the task layer. Reuse the leaf layer. `Task` is only a waker.

**The finding that forces this.** `Std.Async` is not a runtime:

```lean
inductive MaybeTask (α) | pure : α → MaybeTask α | ofTask : Task α → MaybeTask α   -- Basic.lean:327
@[expose] def BaseAsync (α) := BaseIO (MaybeTask α)                                -- Basic.lean:389
```

`bind` is `BaseIO.bindTask`, `wait` is `Task.get`, `asTask` is `BaseIO.asTask`, `await` is
`MaybeTask.ofTask`. There is no queue, no waker, no poll. **Driving `Std.Async` *is* using the stock
pool**, so "put our scheduler under `Std.Async`" is not a smaller project — it is not a project at
all. The task layer is ours by elimination.

**But the leaf layer is reusable and orthogonal to scheduling**: timers, TCP/UDP/DNS, signals,
processes, `Std.Http`, and the `Std.Sync` primitives are externs either way, and reusing them removes
years of surface from our scope.

**The seam.** `Task` is kept as the *external-event and waker substrate only*. An I/O or timer
completion attaches a continuation that pushes back into our inject queue and notifies. That is
Tokio's `wake()` → `inject.push` + `unpark` (`scheduler/current_thread/mod.rs:734`). Our task bodies
are never `Task`s, so they never run on the stock pool. *This bridge is a design proposal, not a
verified fact — it is the one item that must be spiked before it is relied on.*

**Free win.** `MonadAsync t m` and `MonadAwait t m` are typeclasses, so generic combinators
(`race`, `concurrently`, `background`) can be written once and instantiated at `LeanIn.Task`.

### D4 — Queues are lock-per-queue, batch size one, in Tokio's shape.

Each worker owns a queue behind its own `Mutex`; stealing locks the victim's queue and takes **one**
element.

**Why not lock-free.** Lean exposes no atomics — grepped `Std.Sync` and `Init/System`, nothing for
load/store/CAS/fetch_add; `AtomicT` is a monad, not a primitive. So a lock-free deque needs a new
extern family, and its correctness needs weak-memory reasoning that `iris-lean` cannot do (SC only).

**Why the batch size inverts.** Tokio steals *half the queue* because batching amortises a CAS and
the victim is never blocked. Under a lock, batching *lengthens* the critical section and the victim
*is* blocked. Same shape, opposite tuning.

**What is copied unchanged.** The parts worth getting right are all lock-compatible: the bounded
array (256) with overflow into a shared inject queue — bounded *because* of reclamation, which a
fixed array avoids for free — plus the LIFO slot, the idle set, park/unpark, and the coop budget.

**What disappears.** `pack`/`unpack`, the steal ticket, ABA padding, `UnsafeCell`/`MaybeUninit`: the
lock is the ticket.

### D5 — Interface fixed first: one spec, two implementations.

Five operations, agreed before either implementation: `push`, `pop`, `steal` on a queue; `spawn`,
`await` on a task. The pure model and the concurrent implementation carry the same names, which is
what makes refinement stateable. See [`interface.md`](interface.md).

### D6 — Memory model: `seq_cst` only.

No weak-memory reasoning in v1, and none claimed. Lean's runtime uses C++11 `seq_cst` atomics
internally, and `iris-lean` is SC-only. The lock-per-queue design (D4) means we do not depend on
weak-memory behaviour ourselves.

### D7 — The primitive list is closed and small.

Everything the scheduler may trust is enumerated, and anything not on the list is not used.

| Group | Primitives | Backed by |
|---|---|---|
| exclusive access | `BaseMutex.new/lock/tryLock/unlock` | `std::mutex` (`mutex.cpp:27–39`) |
| waiting | `Condvar.new/wait/notifyOne/notifyAll` | `std::condition_variable` (`mutex.cpp:55–69`) |
| clock | `IO.monoNanosNow` | `object.cpp:421` extern |
| external events | `Task` as a waker only (D3) | `object.cpp`, via `IO.Promise`/`BaseIO.bindTask` |

**Deliberately excluded.** Atomics (not exposed). `IO.Promise` (Mutex+Condvar covers it, so it stays
out of the TCB). Thread creation (v1 runs on the caller's thread; D2). `IO.Ref` — see O1.

---

## Closed after M0

### D8 — `IO.Ref` stays invisible behind `Mutex α`.

`Mutex α` is *implemented* as `IO.Ref α + BaseMutex` (`Mutex.lean:120–123`), and `IO.Ref`'s get/set
are not thread-safe on their own. The theory therefore treats `Mutex α` as opaque with `α` abstract:
the axiom is "`atomically k` is an atomic transaction on `α`", and `IO.Ref` never appears in it.

**Rule that follows:** `IO.Ref` is touched only under a lock. Convention now; a wrapper type or lint
later. The alternative — axiomatising `IO.Ref` as a sequentially-consistent cell — was rejected
because it invites reasoning *outside* locks, which is exactly what we would then have to police.

### D9 — A marker type replaces `Send`, for now.

Lean has no `Send`/`Sync`, and Tokio's `spawn` bound is load-bearing: it is why nothing thread-unsafe
crosses a task boundary. Lean would happily accept a `spawn` capturing an `IO.Ref`.

**Decision:** a marker the user must inhabit, checked at the API boundary, in v1. A *proved* property
of a restricted subset — "tasks built only from these combinators cannot race" — is the better end
state, but it constrains the API and is not a v1 cost we should pay. Revisit once the interface has
seen use.

### D10 — The `Task`-as-waker bridge works. O3 closed.

Spiked, not assumed. `WakerSpike.lean`, run three times:

```
  carrier  tid=3185064  consumed "event:ok: 7" (waker tid=3185065)
  waker tid=3185065   carrier tid=3185064
  CHECK distinct threads (the seam) : true
  CHECK carrier not a pool worker  : true
  CHECK waker was a pool worker    : true
```

An external `Task` completes on a pool worker; `BaseIO.bindTask` routes the completion into a
`LeanIn`-style inbox; the work then runs on a dedicated carrier thread. The push and the work happen
on different threads, which is the whole claim.

**Incidental finding, worth keeping:** `IO.println` is `IO Unit`, so it is **not** available inside a
`bindTask` continuation, whose type is `BaseIO (Task β)`. The waker's identity therefore has to travel
as *data* rather than being printed where it is learned — a small but real constraint on any
instrumentation built on this seam.

**Limits of the evidence.** "carrier not a pool worker" and "waker was a pool worker" are checked
against a *sampled* set of pool thread ids (32 trivial tasks), not the pool's actual membership, so
they are suggestive rather than conclusive. The reliable check is the first one — the two threads are
distinct. The claim "dedicated priority implies its own OS thread" rests on the runtime source
(`object.cpp:792` → `spawn_dedicated_worker`), not on this spike.

---

## Open

None. All decisions are closed; D9 should be revisited once the interface has seen use.
