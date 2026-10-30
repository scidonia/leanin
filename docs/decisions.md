# Decisions

Settled decisions and the evidence each rests on. Evidence anchors are in
[`lean-scheduler.md`](lean-scheduler.md) (the current runtime), [`tokio-map.md`](tokio-map.md) (what
we are taking), [`evidence.md`](evidence.md) (the claim-to-source register) and
[`PERFORMANCE.md`](PERFORMANCE.md) (the measured rows the cost records cite). No decision is open: each
entry states its own limits, and the ones D20, D21, D22, D23 and D24 leave are named in them.

______________________________________________________________________

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
| thread creation | `IO.asTask … Task.Priority.dedicated` | `lean_io_as_task` → `object.cpp:792`, `thread.cpp:120` (`pthread_create`) |
| liveness witness | `IO.Promise.new/resolve/result?`, `Task.map` (`sync := true`), `IO.getTaskState` | `lean_io_promise_new`/`_resolve`/`_result_opt` (`Init/System/Promise.lean:40-41,48-49,54-55`), `lean_task_map` (`Init/Core.lean:701-703`), `lean_io_get_task_state` (`Init/System/IO.lean:555`) |

**Deliberately excluded.** Atomics (not exposed). `IO.Ref` — see O1. The direct `IO.Promise` reach is
*not* excluded: the blocking pool's liveness witness is one, on the table's second row above, and O1's
rule is why the witness is a promise and not an `IO.Ref Bool` — an `IO.Ref` read outside a lock is
exactly what D8 forbids.

______________________________________________________________________

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

Spiked, not assumed. `LeanIn/Exe/WakerSpike.lean`, run three times:

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

### D11 — One reactor, and I/O concurrency comes from the blocking pool.

**Rust does not have multi-threaded I/O polling either.** In a `multi_thread` runtime there is exactly
**one** driver, shared by every worker: `Parker` holds `Arc<Shared> { driver: TryLock<Driver> }`, and
the source comment says "Shared across multiple Parker handles", "Only one thread at a time can use
this" (`park.rs:52–53`). Workers `try_lock` it — the winner polls, the losers park on a condvar and
report `HadDriver::No` (`park.rs:89–94`). So Tokio's multi-threading is about *running tasks*
concurrently; **polling is single-threaded.**

Rust gets I/O *concurrency* from elsewhere: `spawn_blocking`, which is how `tokio::fs` is built
(`fs/file.rs:29,407`) — regular files have no readiness notification, so a thread is the only option.
Parallel reactors come from running **multiple runtimes** (thread-per-core), and from io_uring, which
is unstable (`--cfg tokio_unstable`, `io-uring` feature, `runtime/io/driver/uring.rs`).

**Lean is the same shape but stricter.** One process-global loop: `extern event_loop_t global_ev`
(`event_loop.h:32`), initialised once (`initialize_libuv_loop() = event_loop_init(&global_ev)`,
`uv/event_loop.cpp:137`), polled by one thread (`libuv.cpp:26`). There is **no `uv_loop_init` anywhere**
in the runtime, and `Std.Internal.UV.Loop` exposes only `Options`, `configure` and `alive` — 43 lines,
with no way to create a loop. DNS goes to `uv_getaddrinfo(global_ev.loop, …)` (`uv/dns.cpp:73`), and
Lean binds no general threadpool API (`uv_queue_work` appears nowhere in the bindings or the runtime).

**"Multi-threaded I/O" means three different things, and only one is ours:**

| Meaning | Available? |
|---|---|
| **N I/O operations in flight concurrently** | **yes — this is M4.** The blocking pool. No new primitives. |
| N threads *polling* readiness (parallel reactors) | no — needs per-thread-loop externs, and every `lean_uv_*` call goes through `global_ev`, so it bypasses the leaf layer D3 reuses |
| io_uring (multiple queues, multishot) | no — a new extern for the ring; unstable even in Rust |

**Decision:** the blocking pool (M4), with its remit extended to cover **blocking I/O and blocking CPU**,
not just `IO.sleep`. The other two are out of scope.

**Why the first is sufficient.** For *sockets*, one reactor is normally not the bottleneck: epoll
handles very large connection counts on a single loop, and the per-event work is already parallel
because that is the scheduler's job. Multiple reactors are a latency and CPU-locality optimisation
(Seastar, glommio, Monoio), not a scalability requirement. For *files*, a thread pool is not an
optimisation at all — there is no readiness event to wait on, which is precisely why `tokio::fs` is
`spawn_blocking`.

**io_uring is not "just another extern".** Its whole design is two ring buffers mapped into user space
and shared with the kernel, and the ring's head and tail are **atomics shared with the kernel** — the
man page's own submission snippet ends
`atomic_store_explicit(sqring->tail, tail, memory_order_release)`. So adopting it presupposes exactly
the atomics extern and the weak-memory reasoning that D4 and D6 deliberately left out. It is also
Linux-only (libuv buys us macOS and Windows for free), it is *completion*-based rather than
*readiness*-based so it replaces the reactor rather than extending it, and it is disabled by default in
some environments via the `io_uring_disabled` sysctl (kernel 6.6+) and container seccomp profiles.

**The architecture is already agnostic, though.** Whichever way completions are produced, they arrive
at the same place: the inject queue from D3's seam. So io_uring would change *how* an external event
is produced, not *how* a task is scheduled — a good sign that the seam is drawn in the right place.

**Note on A6.** M4 needs threads, and they come from `Task.Priority.dedicated` — i.e. from `Task`,
which D3 already places in the TCB (D13). So A6 as a raw `pthread_create` axiom is *still* not needed
in v1: the blocking pool is built on `Task` rather than spawning threads itself, which was the
condition this note used to carry and is now a fact of the implementation. A6 is therefore *consumed*
through `Task`, and its `needed` column reads `v1 (W4), v2` ([`primitive-theory.md`](primitive-theory.md)).

______________________________________________________________________

### D12 — `List` is the *specification*; a ring buffer is the *container*.

The model's `ring : List α` is not an implementation and must not be read as one. It is the ghost
view, and a separate `Ring` container refines it.

**The container.** `Ring` is a **fixed-size `Array`** of slots plus the index of the oldest live element
and a live count, with:

- `Ring.toList` — the ghost view, oldest first, so every proof is about a list;
- `Ring.WF` — the store's size is `cap`, the live count fits, and the live range is **dense** (no
  holes), so `toList` yields real elements rather than defaults;
- `push` / `pop`, with `push_toList` and `pop_toList` as the laws tying it to the spec.

**`Array`, not `List`, and that is the point of a ring.** `Array.set` modifies in place when the array
is uniquely referenced; `List.set` copies a prefix. `push`/`pop` use `Array.setIfInBounds` so they stay
total and independent of `WF` — `Array.set` demands a bound proof. The `List` appears **only** in
`Ring.toList`, where its algebraic lemmas keep the proofs short. That split is the one Lean's own
containers use.

**The transaction releases the cell's hold before it modifies the pool.** `Array.set` copies when the array is
still referenced elsewhere, and a transaction's `get` leaves exactly one other reference behind — the cell's
own. So a ring mutation under `Mutex.atomically` copies the slots (2 KB at `cap = 256`), and those copies are
most of the garbage the pool produces. Writing a placeholder into the cell first makes the state the
transaction read the only owner, and the mutation happens in place; the computed state is written back before
the lock is released, so nothing outside the critical section can observe the placeholder. Only sites that
*replace* the pool can do this, and the take sites reach the same place by asking the scheduler *before* they
read the pool: under `Aligned` a refusal means an empty pool, so nothing needs restoring and only the accept
path releases the hold. A site that restored a pool it had already read could not: the in-place mutation moves
the value it means to restore.

**Correction: the placeholder is necessary and not sufficient.** A store into a cell another thread can reach
marks the value multi-threaded, and a marked array is never exclusive, so once a pool's cell is shared each ring
write copies the slots whatever the transaction released. Unshared, `Pool.submit` and `Pool.takeFromRing` also keep
`p` alive across the write. The ring's copy is bounded by `cap`; the measurement is `PERFORMANCE.md` §4.9.
**Precedent: Lean's own containers already do exactly this.** `Std.DHashMap` is an Array-of-buckets
implementation carrying a bundled well-formedness invariant, and `Std/Data/DHashMap/Lemmas.lean`
proves its operations against a **`List` model**. Array container, list ghost view, laws in a separate
file — the pattern is the house one, not an invention.

**The check that the spec is faithful, not accidentally quadratic.** The model's operations are
push-back, pop-front, and "move the newer half into `inject`". All three are what a ring does natively —
moving the newer half is `Ring.keepFirst`, `O(1)` and slot-local, which is `push_overflow`'s own move
(`queue.rs:253`). **Nothing in the model requires arbitrary list surgery**, so the list model is a faithful
specification of a ring, and the `O(n)` list operations are spec-level convenience, not a performance
claim about the implementation.

**Where the new difficulty is, stated honestly.** A faithful array model makes push and pop turn on
index arithmetic modulo `cap`. That is a different kind of proof work from the pool's permutation and
chunk reasoning, and it is *isolated*: one lemma (distinct live indices occupy distinct slots) carries
all of it, and the ghost view means nothing downstream ever sees an index.

**⚠️ Where it bit, and how it was resolved.** An attempt at the container was withdrawn, then landed.
`omega` does not reason through `%` — it treats `(head + i) % cap` as an opaque atom — so `slot_ne`
normalises with `Nat.mod_add_mod` and splits on whether each argument is below or above `cap`. **The
`≥ cap` branch must carry its side condition out of the split:** `Nat` subtraction saturates, so a bare
`m % cap = m - cap` is satisfiable at `m = cap = 0` and refutes nothing. With that, the `%`-indexed
formulation — exactly Tokio's scheme — is what shipped, and the compaction alternative is unnecessary.
See M2b in [`PLAN.md`](PLAN.md).

**Consequence for the plan.** `Ring` is a pure, provable obligation and belongs *before* M3's
concurrency, since the concurrent queue is a `Ring` under a mutex. It is scheduled as **M2b**.

______________________________________________________________________

### D13 — Blocking work runs on a pool of our own threads, reached through `Task.Priority.dedicated`.

**What it is, and where it lives.** `LeanIn/Runtime/Blocking.lean` holds a `BlockingPool`: a FIFO
`List (IO Unit)` queue with a `stopping` flag and an `exited` count under the pool's **own**
`Std.Mutex`, workers parked on the pool's **own** `Std.Condvar`, `new (workers : Nat)` starting the
workers and `shutdown`/`shutdownAndWait` ending them. `spawnBlocking (p) (hooks) (act) : Task.Async α`
is the operation, with `spawnBlockingE : … → Task.EAsync IO.Error α` as its failure-carrying sibling.
The handle is the ordinary `Task.Task α` the task layer already gives a spawned computation, so
`await`, `Runtime.cancel` and `concurrently` work on a blocking job with no new handle type
([`interface.md`](interface.md) §4).

**The first new direct external operation, named.** The pool's worker-launch path calls
`IO.asTask (act) Task.Priority.dedicated` (`Init/System/IO.lean:450`, extern `lean_io_as_task`), which
is **A6** — a new OS thread runs the closure, creation *happens-before* its first instruction, and it
is joinable ([`primitive-theory.md`](primitive-theory.md):63). It is named in D7's table as a
primitive, and A6's `needed` column reads `v1 (W4), v2`. Everything else the pool reaches — the lock,
the condvar, the queue — is A1–A5, already registered; the witness's promise calls are D7's second row,
named below.

**The second new direct external operation: the liveness witness.** `spawnBlockingE` reaches
`IO.Promise.new`, `Promise.resolve` and `Promise.result?` *directly*
(`LeanIn/Runtime/Blocking.lean:163-176`), with `Task.map … (sync := true)` as the derived witness and
`IO.getTaskState` as what `Runtime.pending` reads it with, so they are D7's second row: a direct
`IO.Promise` call required its own cited primitive and control (`AGENTS.md`, "Proof and trusted-base
audit"). **Why a promise and not a counter:** `Runtime.pending` must count a blocking job the way it
counts a leaf registration, so the witness has to be a stock `Task Unit` — the shape `Hooks` already
stores — and the count cannot be an `IO.Ref`, because the job thread writes it while the carrier reads
it, and an `IO.Ref` read outside a lock is exactly what D8 forbids. A promise-backed task is therefore
the one shape that needs no second registry and no change to `Hooks`' type. Its control is
`controlWitness` in the default `controls` mode (a witness not `.finished` before `resolve` and
`.finished` after, with a never-resolved promise as the affirmative control), and SC12's `pendingPeak`
and `pendingAfter` are the same property read at the work level.

**It is not a new axiom.** A6 is *consumed* through `Task`, which D3 already places in the TCB; no raw
`pthread_create` is called, so D11's conditional is satisfied by construction. Raw `pthread_create`
through FFI was rejected for exactly this reason — it would add A6 as a raw axiom — and the bounded
pool needs no such call.

**What the pool is not.** *Not a source of boundedness*: Lean creates one OS thread per dedicated
`asTask`, so the boundedness is our own loop, not the primitive's. *Not interruptible, and not
re-joinable by us*: the worker handles are dropped, leaning on `IO.asTask` running a task with no
reference to it, and a running job cannot be stopped from outside. *Not fair, and not bounded in
latency*: A6 gives no scheduling guarantee, so nothing in the pool may be read as promising a job
*will* run or finish. *Not a carrier, and not on the executor's queue*: the pool's threads hold no
executor state and take no items, and `submit` writes the pool's own lock and nothing else, so a job
cannot starve or be starved by the ready queue. `Executor`, `Item` and `Hooks`' type are unchanged.

**The decisions a reader is most likely to need.** Width is the caller's argument, because the runtime
has no configuration surface and a default width would be an unstated policy; there is no global or
lazy pool. The queue is a `List` whose `submit` appends under the lock, so its cost is **O(queue
length)** — a function of the backlog rather than a constant, which is why the round-trip row keeps the
queue short. There is no bound on the backlog: bounding it with back-pressure is its own item — a bounded
blocking pool whose `submit` parks on a capacity, with its own scenario; W6 built the mechanism such an item
would use, a semaphore with a capacity (D14), but back-pressuring `submit` changes its signature and SC12's
accounting and needs its own scenario, so it is named rather than silently taken. **W12's registry is not that
item: a `JoinSet` holds handles and does not bound membership (D16), so it is not a queue meter, and this
backlog stays unbounded.** The trigger to take it is the first server route that submits blocking work from an
unbounded producer, or `submit`'s O(queue length) showing in a measurement with a long queue
(`--runtime-ops`'s submit-alone figure). A submit to a stopping pool **throws**
rather than enqueuing a job no worker will take, which would hang its awaiter. `shutdownAndWait` drains
the queue and then waits for every worker to exit, so a job submitted before the shutdown still runs; a
job that never returns makes that wait unbounded, which is W13's deadline and not a promise here. A
job a caller awaits cannot outlive the driver's stop condition — the driver returns only when its
`finished` predicate holds, and the job's completion is what makes it hold — so `blockOn`'s signature
and its drain wait are unchanged. An abandoned job is not cancelled: it runs to completion, and its
completion item is skipped by `Item.fire` when the submitting computation was cancelled, so a
cancelled computation runs no step of it. `Runtime.pending hooks` counts a blocking job, because the
step registers the job's liveness witness in `Hooks` exactly as a leaf registration does; the pool's
own counts stay on the pool, under its own lock.

**The remit, and what is not in it.** The pool is for the leaves that genuinely block — file I/O, the
synchronous APIs (`IO.FS`, `IO.sleep`), foreign or CPU-heavy calls — and **not DNS**: `uv_getaddrinfo`
runs on libuv's own pool (`tokio-workplan.md:289-290`), so that leaf is already off-carrier, and Lean
binds no general threadpool API to duplicate. The pool exposes `submit` and no file API, so it stays
**bounded and separable** rather than baking file I/O into it (`tokio-workplan.md:52-53`) — this is the
line to check when a leaf is added, and it lives here rather than only in `Blocking.lean`'s module doc.

**Its control.** A6's control is `controlDedicated` in the default `controls` mode: a dedicated `Task`
reads a value written before its spawn, reports a tid distinct from the caller's, and is `IO.wait`ed.
SC12's off-carrier detector reads the same fact where the work ran, and the standing `dedicat` row
prices a thread per job.

______________________________________________________________________

### D14 — The sync primitives are the task layer's own mechanism on `Join`; the `Std.Sync` adapters are rejected.

**What it is, and where it lives.** `LeanIn/Task/Sync.lean` holds an async mutex, an async semaphore and a
bounded channel. A `Semaphore` is a permit count and a waiter list under one `Std.Mutex`; a `Mutex` is a
semaphore of one permit; a `Channel α` is a bounded FIFO queue with a sender list and a receiver list beside it,
and a capacity the caller supplies — the runtime has no configuration surface, so a default bound would be an
unstated policy. Awaiting operations (`Mutex.lock`, `Semaphore.acquire`, `Channel.send`, `Channel.recv`) are
`Task.Async`; operations that cannot park (`Mutex.tryLock`, `Semaphore.tryAcquire`, `Channel.trySend`,
`Channel.tryRecv`) are `IO` — the same split as `Join.resolve` against `Async.await`. `Channel.new` refuses a
capacity of zero, loudly, as `BlockingPool.new` refuses a zero width: a channel that can hold no value serves no
sender, and a rendezvous needs a different shape than a buffer.

**The mechanism, and the one idea it turns on.** A wake is a *hint*, never a hand-off. An operation that cannot
be served registers its own fresh `Join` (made before the lock, so no lock is taken while holding another) and,
outside the critical section, parks with `Join.onReady`; its continuation re-enters the operation's step through
`ctx.resume`, so the retry is a step stamped with the waiting computation's own token
(`LeanIn/Runtime/Basic.lean:26`). A release — or a `recv` that frees room, or a `send` that fills a slot — takes
the whole waiter list, clears it inside the critical section, and resolves each taken cell with
`Join.resolveFirst` *outside* the lock; the woken waiter re-reads the state and either acquires or registers a
fresh `Join` and parks again. The cost is O(w) wakeups per release where w is the number of parked waiters; it is
measured (`docs/PERFORMANCE.md` §3.1), and it is not a fairness guarantee.

**Why the `Std.Sync` adapters are rejected.** The workplan's premise was that the semaphore and the channel are
adapters over what exists. They cannot be, because both stock shapes hand what a waiter asked for to that waiter
*irrevocably*: `Std.Sync.Semaphore.release` dequeues a waiter and resolves the promise it parked on
(`Std/Sync/Semaphore.lean:76-87`), so the permit is gone whether or not that waiter ever runs again, and
`Std.Sync.Channel.recv` dequeues the message into the `Task` it returns (`Std/Sync/Channel.lean:542-546`),
before any awaiter is resumed. Our cancellation gate is `Item.fire` (`LeanIn/Task/Basic.lean:99-100`), which
skips a cancelled computation's step — but it cannot un-resolve a promise or re-enqueue a dequeued message, so a
waiter whose token is set between the hand-off and its resumed step consumes a permit or a message it is never
granted. This is the milestone's sharpest finding, and it is why W6's "adapters over what exists" sentence is
corrected. A `Std.Sync.Notify`-based channel is rejected for the same reason in a different shape: `notifyOne`
resolves one consumer's promise, so a cancelled consumer's notification is lost. A blocking `Std.Sync.Mutex` is
the other half — `BaseMutex.lock` is `opaque` (`Std/Sync/Mutex.lean:39`), A1's C++ `std::mutex`, so taking it on
the carrier wedges it.

**The law the mechanism satisfies.** A cancelled waiter is granted nothing and consumes nothing: it was never
granted a permit (the wake only enqueued a step, and `Item.fire` skips it), and a cancelled sender enqueues
nothing and a cancelled receiver consumes no message, because each acts only inside its own step. Nothing
changes in `Hooks`: a sync waiter is a *computation*, not a leaf registration — its wake is produced by another
computation's step on the carrier — so there is nothing to retire, and `Runtime.pending` therefore does not count
a parked lock waiter. That residual is stated rather than hidden, and it is what W13's deadline is for.

**What it does not touch, and what it does not promise.** `Sched.Executor`, `Task.Item` and `Hooks` are
unchanged; items are built with `Item.ofAction` as everywhere else, and the only new item is the retry step,
stamped by the same `Ctx.resume`. There is **no** `MutexGuard`/RAII release (Lean has no drop hook that could
release, so a guard would silently never release, and guarding a value stays the caller's business), **no** owner
or reentrancy check (a mutex is one permit; an `unlock` by a computation that did not `lock` is undetected),
**no** `close`/`Broadcast`/`select`/`Notify` or cancellation-token surface, and **no** fairness or FIFO promise
for waiters — the queue is FIFO, the waiter order is not (§5 of [`interface.md`](interface.md)). A capacity of
zero is refused rather than silently serving nothing.

**The model obligation, stated and deferred.** A semaphore does admit a real invariant — over
`{ permits : Nat, holders : Nat, waiters : List Id }`, `permits + holders = capacity` under the discipline that
every acquire is matched by one release, plus the cancel property "a computation whose token is set never
transitions from parked to holding". It is deferred, with reasons: it would add no primitive (the mechanism is
one `Std.Mutex` critical section per operation, the same class as the blocking pool, which took no model); the
safety conjunct is a one-line arithmetic invariant over lists and naturals, and the cancel conjunct is discharged
by the task layer's *existing* gate — acquisition is a step, and `Item.fire` skips a cancelled computation's
step, which SC11 already asserts at the boundary; and a model with no refinement theorem proves nothing about the
code, while the refinement needs the serializability lemma (`docs/primitive-theory.md` §4) applied to the sync
critical sections — materially larger than W6's acceptance. **Trigger to take it:** before a primitive gains a
`close`, broadcast or select surface, or before the sync layer is used by a server whose liveness is argued —
then `LeanIn/Model/Sync.lean` with that invariant and a reachability probe in the idiom of
`LeanIn/Test/Dynamics.lean`.

**The register and the TCB are unchanged.** The mechanism reaches `Std.Mutex.new`/`atomically` (A1, D7's first
row) and pure list and natural-number code; it reaches no `IO.Promise`, so it adds no citation and needs no
control of its own, and `Blocking.lean`'s direct promise reach stays the only one. A direct `IO.Promise` call
would have owed D7's second row a cited primitive and a control; the waiter-queue mechanism does not, and neither
does the staged adapter revision that preceded it (it went through `Std.Sync` and
`Std.Async.AsyncTask.ofPromise`). `Cancel.isSet` is `IO.Ref`-backed and is read *inside* these critical
sections — the sync layer's only read is the private `live`, called under `st.state.atomically` — while the
token's *write* (`Cancel.set`, from `Task.cancel`) is the unsynchronized half, taken under no state lock. That
asymmetry is a pre-existing fact of `Task.Cancel` (`LeanIn/Task/Basic.lean:42-`), whose doc already states that a
second carrier is where it becomes a race — so the new code inherits that comment rather than adding a new
instance. Until W8, no sync primitive may be read as cross-carrier-safe.

The request cancellation the HTTP driver now has (D23) is **not** `Task.Cancel`: it is a typed abort raised by
the operation that observed the peer's failure, in the step that observed it, and it neither reads nor writes
this token, so nothing here changes and the register stays as it is.

______________________________________________________________________

### D15 — The service's obligations are proved over the model; their refinement to the executor is argued, with an executable correspondence test.

**What it is, and where it lives.** W14 states the three obligations a *server* has and checks them at the
executor boundary. The model is [`LeanIn/Model/Service.lean`](../LeanIn/Model/Service.lean), pure and decidable
over a `Service` state keyed by connection *identities* rather than counts. It carries five invariants:
`Service.WF` (the well-formedness the others sit on), `Service.NoDrop` (the partition of the admitted ids over
`live`/`completed`/`closed`), `Service.Bounded` (`live.length ≤ bound`), `Service.RequestsResolved`
(`responded + errored + pending.length = requests`) and `Service.PendingWithinLive` (`∀ i ∈ pending, i ∈ live`).
Each is proved over the `Service.Reachable` inductive — `reachable_invariants`, with `reachable_noDrop`,
`reachable_bounded`, `reachable_requests` and `reachable_pendingWithinLive` as its per-obligation projections —
and matched by a breaking-control that makes one invariant false (`abandon_breaks_noDrop`,
`acceptBeyondBound_breaks_bounded`, `closeDropping_breaks_requests`). The three obligations are: (1) every
accepted connection is either completed or closed and never silently dropped; (2) the number of live connections
never exceeds its bound; (3) every request gets a response or an error within its deadline. The executor's
product is `Runtime.serveBounded` ([`LeanIn/Runtime/Net.lean`](../LeanIn/Runtime/Net.lean)), an accept loop that
admits at most `bound` connections at a time.

**The decision: W14 takes the sanctioned fallback, and does not attempt a refinement theorem.** The model is
proved; the step from it to the running code is argued in prose with an executable correspondence test — the
fallback of [`proof-strategy.md`](proof-strategy.md) §5 (T1) and the instrument P8's own row names. The reasons
are the repository's own: Lean's `IO` has no concurrent semantics (Gap A), so a refinement proof would mean Iris
over a modelled language that is not Lean's; the serializability argument that links the two columns
([`primitive-theory.md`](primitive-theory.md) §4) is itself an argument, not a theorem; and proving the model
while arguing the refinement is honest precisely when the argument is a first-class document with an executable
correspondence test.

**The mechanism, and why the bound is a permit.** The bound is the service's obligation, and
`Task.Sync.Semaphore` (W6, D14) is built for the shape: a wake is only a *hint* and a permit is taken in the
waiter's own step, so the loop can never be handed a permit it then skips. `serveBounded` takes a permit before
each `Listener.accept`, spawns the body, and releases it when the body ends — on the body's own tail and on a
caught failure, with a failing `accept` releasing before the failure travels. `EAsync`'s bind short-circuits on
`error`, so exactly one release runs on every path a body can take. The model's `accept` has no transition at the
bound; the loop's permit is the same statement in the executor. SC14 reads the bound's projection from the mode's
own `begin`/`end` annotations, not from a clock.

**The correspondence.** [`interface.md`](interface.md) §6 pairs each obligation with the declaration it refines
and each model operation with its executor counterpart: `Service.accept` with the loop's
`tryAcquire`-then-`accept`, `Service.request` with the body's `recv`, `Service.respond` with the echo,
`Service.deadline` with `withTimeout` returning `none`, `Service.complete` with the body's `.ok`, and
`Service.close` with the body's `.error`. It is an argued correspondence: the refinement theorem
`Impl.op ⊑ Model.op` remains open (P8).

**The two limits, stated where the guarantee is read.** Both are findings, not fixes.

1. **Only the success-path permit release is exercised by SC14.** The wrapper releases on the body's own tail,
   on its error branch for a body that propagates a failure, and on a failing `accept`. The mode's body catches
   its own failures at the connection boundary, so every body in the scenario returns `.ok` and the wrapper's
   error branch is unreachable there. Its totality is **by construction** — `EAsync`'s bind short-circuits on
   error and the failure branch releases before re-raising — not by an observation. A failing body would have
   changed the scenario's staging and fields, so the limit is recorded rather than demonstrated.
2. **A cancelled body's release step is skipped by `Item.fire`, so a permit can leak.** Cancellation is explicit
   and step-scoped (W5, D14): a body whose continuation is cancelled never reaches its release. This only
   *reduces* admissions — a leaked permit can never push `live` past the bound, so `Service.Bounded` still holds
   and obligation 2 is **not weakened**; what is lost is the **liveness** of admission, since a service that
   cancels many bodies can slowly stop admitting. It follows from the cancellation gate, not from a defect in
   `serveBounded`. SC14 exercises no cancellation. D23's request abort is a different mechanism — a machine
   value raised in the step that observed the peer's failure — and it does not reach this gate.

**What it does not claim.** Not that the executor is a refinement of the model (argued, not proved); not the
liveness half of "within its deadline" — that a pending request *eventually* reaches its deadline is P9-class and
not provable from A1–A7 ([`primitive-theory.md`](primitive-theory.md) §6), so obligation 3's `deadline`
transition is shown to exist, to be enabled exactly for a pending request, and to have an executor witness that
is observed to fire, and nothing more; not that the connection↔task correspondence composes the executor's own
single-carrier invariants (`Sched.Executor`'s `State.Aligned`) — the model is deliberately above the pool; not
cross-carrier ([`interface.md`](interface.md) §5); not HTTP.

**D14's trigger, partially activated and restated.** D14 deferred the semaphore's own invariant
(`permits + holders = capacity`) with a trigger reading "before ... the sync layer is used by a server whose
liveness is argued". W14 uses the semaphore at a server boundary, so that trigger is now partly pulled: the
service-level obligation `Service.Bounded` is what W14 needs and proves, and the semaphore's finer invariant
stays deferred, because it would add a second statement whose refinement is the same P8 gap and would discharge
none of W14's acceptance. The remaining trigger is unchanged — take `LeanIn/Model/Sync.lean` before a primitive
gains a `close`, broadcast or select surface, or before the semaphore's *liveness* (not merely its bound) is
argued, which is exactly where limit 2 above lives.

**The register and the TCB are unchanged.** `serveBounded` adds no primitive and no citation: its mechanism is
`Task.Sync.Semaphore` (one `Std.Mutex` critical section, A1) over `Listener.accept`/`Conn.recv`/`Conn.send`
(W1's socket seam) and `Runtime.withTimeout` (W3's timer leaf, `Std.Async.sleep`). No atomics, no `IO.Promise`
reach, no new syscall, so D7's register is unchanged and `Blocking.lean`'s direct promise reach stays the only
one; [`primitive-theory.md`](primitive-theory.md) §6 records the non-change, and `#print axioms` for the new
theorems is clean.

**_Trigger to take the refinement theorem._** Build a deterministic service driver whose accept/completion
interleaving is fixed by construction, or find a concurrent `IO` semantics to host the refinement — then replace
the argued correspondence with `Impl.op ⊑ Model.op` and the SC14 detector with a pairwise comparison against a
`tests/ServiceOracle.lean`. SC14's detector shape is what is available at W14 and is not faked as more.

______________________________________________________________________

### D16 — The task-local context is a typed field of `Ctx`; the registry is a `JoinSet` and drains by awaiting.

**What it is, and where it lives.** `LeanIn/Task/Basic.lean` carries a typed `Local` record — `requestId`,
`deadline`, `trace` — as a third field of `Ctx` (`Ctx.local`), with `Async.local` (a field read of the immutable
`Ctx` a step already holds, `:220`) and `Async.withLocal` (`{ ctx with local := l }` on a computation's steps,
`:225`) as its operations. `LeanIn/Task/Registry.lean` is a `JoinSet`-shaped set of handles: one `Std.Mutex` over
a membership `List`, with `new`, `add`, `spawn`, `size`, `joinAll` and `drain`. It is task-layer code like
`Sync.lean`, because its members are computations and its operations are steps of computations; it holds no
executor state and no leaf registration, so `Runtime.pending` does not count a registered handle. `Net.lean`'s
three serving loops use it — `joinAll` in `serveNJoin`, `drain` in `serveUntilStopped`/`serveBoundedLoop` — keeping
their public signatures, which is what makes shutdown a *drain operation* rather than a caller's `List.forM`.

**The inheritance rule is one line, at the one place a child's `Ctx` is built.** `Async.spawn`'s child takes
`local := ctx.local` (`LeanIn/Task/Basic.lean:263`), so a computation inherits the innermost enclosing `withLocal`
value at its spawn site; `Runtime.Basic`'s two `Ctx` sites take the default, because a spawn from outside a body has
no parent context and the driver's own computation has none. `Ctx.local` has **no default**, so the compiler visits
every construction site and the inheritance rule is a reviewed line rather than a silent omission; `EAsync` needed no
change, because its lift threads `ctx` through, so the error layer inherits the context the moment the one line
lands. **Rejected: a name-keyed heterogeneous store** (`Map String Dynamic`, Tokio's `task_local!` surface) — its
reads are unchecked casts a reader and a writer must agree on by convention; it needs its own lock for a read the
typed field makes a field read of an immutable value; it has no structural inheritance, because a child needs a deep
copy or a shared mutable map, and shared mutable state across computations is what D8 and D9 refuse here; and
`task_local!` is itself a macro that gives each key its own typed cell, of which a typed record is the degenerate,
checked case. **Rejected: a field of `Item`** — an `Item` is a step, and every step is built with the `ctx` it runs
with, so a field would be a second copy that could disagree with the closure's. **Rejected: parameterising `Ctx` by
the local's type** — it would ripple through `Async`, `Item`-stamping and four public signatures to buy a second
store the reasons above reject.

**Drain semantics, and the three laws.** Every registry operation is a critical section over pure list code; the
awaits happen *outside* the lock, on a snapshot the lock has released, because running a continuation inside would
enqueue — which takes the executor's lock — while holding this one (`Join.resolve`'s rule, restated). `drain` takes
the whole membership and clears the registry in one critical section, then awaits each taken handle outside it. The
registry is **unbounded by decision**: a `JoinSet` holds handles, it does not meter admissions — the connection
limit stays the proved semaphore in `Runtime.serveBounded` (D15), so a second bound would be a second place the
limit lives and would make `add` a parking operation, wrong for a drain path. **Consistency with W5 and W6:** a
cancelled handle's cell is resolved by `Task.cancel` through `Join.resolveFirst` (`LeanIn/Task/Basic.lean:250`), so
`drain`'s await on it takes `Async.await`'s "already there" path rather than parking — a drain cannot leave a caller
awaiting a handle forever; a handle parked on a leaf is retired by `Runtime.cancel`, so a drain over a cancelled
connection does not keep `Runtime.pending` non-zero; and the registry transfers **nothing** — no permit, no message,
no queue slot — so W6's wake-is-a-hint law holds vacuously, stated rather than assumed. **What `drain` does not do
is cancel:** the deadline arm of W12's "Why" sentence is `Runtime.cancel` per handle, issued by whoever holds the
clock, and the registry's contribution is only that it then drains.

**Deferred: the deadline arm, with its trigger.** "Cancel what outlives the deadline" is deferred to **W13**,
because testing "outlives the deadline" without a harness clock is a sleep, which this repository accepts nowhere.
The deadline that will decide it is `Local.deadline` — the reason the field is in the local at all. A
`Registry.shutdown`/`abortAll` (an operation that cancels what it holds) is **deliberately absent**: its
cancellation half is `Runtime.cancel`, already public, and its test needs W13's clock; adding it now would be an
untested export, which `Net.lean` records this repository deleting rather than keeping.

**Deferred: D13's blocking-pool backlog, corrected.** D13's debt is `submit`'s cost being O(queue length) and its
backlog unbounded. W12's registry does **not** answer it and is not "a registry of that shape": a `JoinSet` is
unbounded membership, a set of handles, not a queue meter, and bounding the pool is back-pressure on `submit` — a
different object with its own observable. D13's row carries the correction and the trigger to take the pool item.

**The model obligation, stated and deferred.** Two propositions are written down in `LeanIn/Task/Registry.lean`'s
module doc and here. `Registry.Sound`: under the discipline that every `add` is followed by exactly one
`drain`-take, at quiescent points `held.length + drained.length = added.length` and `drained` has no duplicates.
`Local.Inherited`: a computation's `ctx.local` is the innermost enclosing `withLocal` value at its spawn site. They
are **argued, not proved**, and the reasons are D14's: both are by construction and have no state to reason about —
`held` is one `Std.Mutex`-guarded `List` whose `add` and take are single critical sections, and on one carrier (D2)
steps do not interleave, so the arithmetic is a list lemma about an append and a take; `Async.spawn` copies
`ctx.local` into the child and every continuation closes over the `Ctx` that built it, so `Local.Inherited` is the
termination rule of the term, not a property of runtime state — and a model with no refinement theorem proves
nothing about the code, while the refinement needs the missing serializability lemma (`primitive-theory.md` §4).
**Trigger to take a model:** before `Registry` gains a bound or a `shutdown`, or before a server's liveness is
argued from a drain deadline (W13) — then `LeanIn/Model/Registry.lean` with `Registry.Sound` and a reachability
probe in `LeanIn/Test/Dynamics.lean`'s idiom. The executable half taken instead is SC15, which reads the drain's
"returns only after the handlers finished" from the mode's own annotations; no model record is computed and
`tests/ModelOracle.lean` is untouched.

**The one stated limit: the liveness half of a drain is not provable.** That a `drain` *terminates* requires that
a handler neither finishes nor is cancelled — a liveness property not derivable from A1–A7
([`primitive-theory.md`](primitive-theory.md) §6). A handler that never returns makes the drain unbounded, exactly
as `shutdownAndWait`'s unbounded wait is stated in `Blocking.lean`. And the local-context law is structural and
argued, not proved: it is tested by inheritance and non-inheritance on one carrier (SC15-O1), and the other-carrier
case is W8's.

**The register and the TCB are unchanged.** The library code this milestone adds reaches no new direct external
operation, checked by inspecting calls and import edges rather than by text search: `Local`/`Ctx` are pure
structure, and `Registry` reaches only `Std.Mutex.new`/`atomically` (A1, D7's first row) over pure list code
(`Registry.lean` imports `Std` and `LeanIn.Task.Basic`). No `IO.Promise`, no `IO.asTask … dedicated`, no
`BaseIO.bindTask` in it; the SC15 mode's gates are the synchronized fakes the test modes already use, not a library
reach. D7, [`primitive-theory.md`](primitive-theory.md) §5 and [`proof-strategy.md`](proof-strategy.md)'s
trusted-base table are unchanged, and `#print axioms` is unchanged because W12 adds no theorem.

______________________________________________________________________

### D17 — `select` is one shared cell on every handle; `race` is the runtime layer that cancels; priority is a placement lane.

**What it is, and where it lives.** `LeanIn/Task/Basic.lean` gains two task-layer combinators.
`select (h : Task α) (hs : List (Task α)) : Async (Nat × α)` is homogeneous and non-empty — head-and-rest, so a
zero-handle selection is unrepresentable rather than a checked error — and returns the winner's index into the
list as given and its value. `join (hs : List (Task α)) : Async (List α)` is `hs.mapM Async.await`, with
`join [] = pure []`; the pair case stays `concurrently` (`Basic.lean:332`). `LeanIn/Runtime/Leaf.lean` gains
`race {α : Type} (hooks : Hooks) (v : α) (h : Task α) (hs : List (Task α)) : Task.Async (Nat × α)` beside
`cancel`. `LeanIn/Runtime/Basic.lean` gains `inductive Priority | high | normal` and changes `spawn` to take it.

**One shared cell, registered on every handle — not one cell per handle joined afterwards.** `select` makes one
fresh `Join (Nat × α)` and, for each handle `t` at list index `i`, calls `Join.onReady t.cell (fun v =>
Join.resolveFirst j (i, v))`. The winner is the first `Join.resolveFirst` — the law already stated at
`Basic.lean:135`, whose doc names this race ("the first of them is the result", "what a timeout or a
`select`-shaped operation needs"). This reuses the law rather than restating it: a resolution that arrives while
`select` waits resolves the shared cell, and a later one is ignored, so the mechanism is the existing
first-writer-wins cell and not a new race account. **The tie rule follows from `onReady`'s immediate path:** if a
handle is already resolved when its registration runs, the continuation runs at once, in list order, so among
handles already resolved at the call the earliest in list order wins, and among handles resolved afterward the
first resolution wins. `select` then mirrors `Async.await`'s "already there" path (`Basic.lean:277`): if the
shared cell is resolved at the end of the registration loop it calls `k` in-step, costing a lock and no
scheduling round. **Rejected: one cell per handle, joined afterwards.** It would need a second race to decide
which of the per-handle cells resolved first, and that second race is exactly the shared cell; and it would
either park on each cell in turn (which the head-only first cut does, and cannot see a later handle) or rebuild
`resolveFirst` per handle. **Rejected: `select` as a `MonadAwait` method.** The class deliberately hides the
cell behind `Handle` (`Basic.lean:312-316`), and `select` needs the cell; a method would force every
implementation to have one for a second implementation that does not exist. **Rejected: `select` over
`List (Task α)` returning `Option (Nat × α)`.** It makes a zero-handle selection total at the cost of an arm in
every caller; the repository's taste is to make the bad state unrepresentable (`interface.md:281`). **Rejected:
the heterogeneous `select!`-shaped surface** (`Sum`-nested branches): Lean's `do` notation does not expand
branches as Tokio's macro does, so it would need an n-ary sum type and a per-arity combinator for a generality no
caller exercises.

**`select` does not cancel; `race` is the layer that does.** A `Task` is a value whose cell is the value's home,
so a handle passed to `select` is still awaitable elsewhere: `select` transfers no ownership and leaves every
loser running, and a caller that wants "wait for the first of several, then continue with the rest" keeps the
handles. `race` is `select` followed by `cancel hooks t v` for every non-winner, so **every observable claim
about a cancelled loser is W5's law's consequence and not a new law about selection**: the loser's cell resolves
with `v` exactly once and immediately (`Join.resolveFirst`), no step of it runs afterwards (`Item.fire`,
`Basic.lean:99`), and its registrations are retired (`hooks.retire`, `Leaf.lean:77`). A loser that finished
before the race returned keeps its own value, because `resolveFirst` ignores a second resolution and a
cancellation never replaces a value that exists. `race` lives in the runtime because cancelling needs `Hooks` to
retire a loser's registrations and the task layer has none. **Rejected: `race` in the task layer** — it would
either duplicate the registry or cancel without retiring. **Rejected: a `select` that cancels its losers** (what
Tokio's `select!` does when the unselected branch owner drops the future) — this repository's cancellation is an
explicit operation with a caller-supplied value (`Task.cancel`, `Basic.lean:248`), and a selection that cancels
makes the mechanism do policy the caller cannot see. There is **no second abandonment mechanism**: `race`
composes `select` with the existing `Runtime.cancel`.

**Priority is a placement lane, and it routes through the two existing destinations.** `spawn (e : Executor cap)
(prio : Priority) (a : Task.Async α)` branches on the argument: `.high` places the task's first step with
`Executor.spawnBase` (`Executor.lean:159` → `Pool.spawn`, the one-slot LIFO buffer), `.normal` with
`Executor.submitBase` (`Executor.lean:93` → `Pool.submit`, the FIFO ring). The two destinations are the two
placements the model already states and the refinement already proves (`toModel_spawn`, `toModel_submit`), and the
new producer routes **through** them rather than opening a third: this satisfies the rule that all producers go
through one internal scheduling-destination decision, because the two lanes *are* those two destinations and the
producer writes the pool through nothing else. **Operationally, "priority"
means: place the task where the queue serves sooner. It does not mean the task will run sooner.** The slot holds
one task, so a second `.high` spawn displaces the first through the same overflow rule `Pool.spawn` applies;
"high" is not a total order and nothing about it is promised. **Rejected: priority as a field on `Item`, or a
priority-ordered ring/inject** — it changes the pool's stated FIFO/ring semantics and needs new model functions
and proofs, to promise an order the interface must not promise. **Rejected: priority on the task-layer
`Async.spawn`** — the task layer has no queue to order (it calls `ctx.resume`, the parent's route), so the
argument would be accepted and ignored, and `Async.spawn` has many callers.

**The model question, answered.** The priority argument needs no new model structure: it selects between two
placements the model already refines, and the served order is already `Model.Pool.take`'s
(`Model/Pool.lean:94-103`). The milestone adds one derived lemma,
`Model.Pool.take_slot_first (p) (x) (hl : p.lifo = some x) (hp : p.lifoPolls < p.lifoCap) : (p.take).1 = some x`
— a one-line restatement of the definition — and its hypothesis is **reachable and staged by a real operation**,
not hand-filled: `example : ((emptyPool Nat).spawn 7).lifo = some 7 ∧ ((emptyPool Nat).spawn 7).lifoPolls < 3 :=
by decide`, so the slot is populated by local `spawn` before the property is claimed. `#print axioms
LeanIn.Model.take_slot_first` is **empty**: the proof resolves the definition's `if` with `ite_eq_left` (the
non-deprecated replacement for `if_pos`), not with `simp`/`split`, which pull in `propext` or
`Classical.choice`. What that list does and does not see: it is dependencies, not hypotheses, so an axiom-free
line means "nothing was assumed as an axiom", never "nothing was assumed". **The priorities themselves are not
in the model**, and must not be: a modelled priority ordering would be the fairness statement `interface.md` §5
forbids. What the model states is the *mechanism* — the slot is taken before the ring while the allowance lasts;
the order a priority argument produces is an instance of `take_slot_first`, not a new property. **Rejected: a
dedicated `LeanIn/Model/Select.lean`** — `select` resolves a `Join` through a law that already exists and adds no
scheduling, so a model file would state no property the `Join` laws do not.

**The register and the TCB are unchanged.** Checked by inspecting calls and import edges rather than by text
search. `select`/`join` use `Join.new`/`Join.onReady`/`Join.resolveFirst`/`Join.value?` (a `Std.Mutex` inside
`Join`, A1) and `ctx.resume`; `Task/Basic.lean`'s imports are unchanged (`Std`, `LeanIn.Sched.Executor`).
`race` uses `Runtime.cancel` → `Task.cancel` (`Join.resolveFirst`) + `Hooks.retire`, with no new promise call.
`spawn`'s priority uses `Executor.spawnBase`/`submitBase` (a `Std.Mutex` and a `Std.Condvar`), both shipped. No
new `IO.Promise` construction, no new `_root_.Task` call path, no new extern, no new import edge into
`Std.Async`. D7's register and [`proof-strategy.md`](proof-strategy.md)'s trusted-base table are therefore
unchanged, and [`primitive-theory.md`](primitive-theory.md) gains nothing.

**Deferred: the heterogeneous `select` and the deadline arm, with their triggers.** The `Sum`-nested/`HList`
shape is deferred until a caller needs to select across handle types (the deferred trigger is W8's multi-carrier
surface and a server racing a request against a *typed* deadline). The deadline arm — `select` given a handle a
timer resolves — is **W13's**: it needs the clock W13 builds, and a deadline parameter here would be a clock this
milestone does not have. `interface.md` §5 records both as the residual absences.

______________________________________________________________________

### D18 — A handle is a narrowed capability, the counters are read through the model projection, and time is injected.

**What it is, and where it lives.** `LeanIn/Runtime/Basic.lean` gains `Handle` (`handle`, `spawn`, `stop`,
`metrics`), `Metrics`/`CarrierCounters`, `Executor.newMetered`, `Executor.counters`/`accrue`, and the general
driver `blockOnWith`/`runWith` (`blockOn`/`run` become that driver with a hook that reports nothing).
`LeanIn/Runtime/Clock.lean` is new: `Clock`, `Clock.live`, `HarnessClock` (`new`, `now`, `pending`, `schedule`,
`advance`, `clock`) and `runVirtual`. `LeanIn/Runtime/Time.lean`'s `sleep`/`withTimeout` take a `Clock`.
`LeanIn/Runtime/Leaf.lean` gains `awaitSignal`. `LeanIn/Task/Basic.lean`'s `Cancel.counter` moves under a
`Std.Mutex`. The scenario is SC17, one mode `--runtime-handle` with the records `handle|`, `clock|`, `signal|`,
`tokens|` and the checker record `handlectl|`.

**The handle is a narrowing, not a `Send` stand-in.** `Handle α cap` holds the executor and exposes exactly
`spawn` (build the child's item and route it through `Executor.spawnBase` for `.high` or `Executor.submitBase`
for `.normal`, D17's two placements), `stop` (`Executor.stop`) and `metrics`. The executor is a **private field
and the constructor is private too**, so the narrowing is enforced by the type rather than documented: from
outside the module a caller can neither project the executor out, build a `Handle`, nor match one apart, so the
three operations are the whole of the surface. The interesting content is what it
**withholds**: `Executor.work`, `Executor.park`, `Executor.tryTake`, `Executor.snapshot`, `serveUntilStopped`'s
executor argument and every `Hooks` operation are carrier-side and are not reachable from a `Handle`, so a thread
that is not a carrier can originate work and ask the runtime to stop without being handed the executor. The claim
that makes it usable off-carrier is `Handle.CriticalSections`: every field of shared state an operation reachable
from a `Handle` reads or writes is read or written inside a critical section of the one lock that guards it, and
every lock on the path is one of A1's. Audited cell by cell — `state` (itself), `cv` (only inside a `state`
section), `Cancel.counter` (after the fix), `Join`'s own lock, and the counters — so a handle operation's critical
sections are serializable against a carrier's, and `State.Aligned`/`Scheduler.Live` survive a foreign-thread
spawn. `Executor.submitBase`'s `notifyOne` is issued inside the same `state` critical section that writes the pool,
which is the lock the parking predicate is re-checked under, so a spawn from a parked-against thread cannot be
lost. **Argued, not proved**, exactly as D14/D15/D16's propositions are: the refinement needs the serializability
lemma [`primitive-theory.md`](primitive-theory.md) §4 states as unproved, so the audit is the whole of what is
claimed. **This is not O2**: a `Handle` is not a `Send` marker, it neither checks nor restricts what a caller
shares with a thread, and it fixes one object on one carrier (D2). Sharing an `IO.Ref`, a `Hooks`, a registry or a
`Join` cell across threads remains exactly as unsafe as it was.

**The allocator fix is D8's rule applied to a cell that was outside it, and it is a control with a reading.**
`Cancel.new` (`LeanIn/Task/Basic.lean`) read `counter.get`, then `counter.set (n + 1)`, under no lock — a direct
`IO.Ref` read-modify-write, which D8 ("`IO.Ref` is touched only under a lock") forbids. It went unnoticed because
with one carrier every spawn ran on that carrier and nothing interleaved it; the handle makes a spawn from a
foreign thread reachable, and the read-modify-write is then a race to two tokens sharing one id — which `Hooks`
attribution and a retire both read by id. The fix is `counter : Std.Mutex Nat` with the read-modify-write in one
`atomically`; it is a correction, not a new primitive, and A1 already covers it. **The finding is observed, not
read**: the mode's `tokens|` control, taken before the fix, printed `contended=128|contendedDistinct=126` — two
duplicate ids in 128 contended allocations by two foreign threads — while `sequential=64|sequentialDistinct=64`.
The **sequential** reading (`n` `Handle.spawn`s on the non-carrier thread give `n` distinct ids) is deterministic
and fails if a duplicate is ever handed out; the **contended** reading is sound because the lock is the guarantee,
and it can pass on an unfixed allocator when the interleaving goes luckily, which is why it is a control and the
fourth `handlectl|` variant rather than one of the clause assertions. `check_sc17` evaluates the three clauses
before this control for that reason.

**The counters are read through the model projection, so a counter cannot disagree with the model.** `Metrics` is
`ready`, `parked` and `carriers : Option (List CarrierCounters)`; `ready` is `pool.inFlight`, which `State.Aligned`
proves equals `sched.work`, `parked` is `sched.parked`, and `Executor.observe` reports the model projection's
own two fields — `work` and `parked` out of `Scheduler.toModel`, the scheduler half of `State.toModel` — read in
one critical section that mutates nothing, enqueues nothing and notifies nobody, so a read cannot perturb what
it measures. `carriers[i]` is `fired` and
`busyNanos` per carrier, index 0 while there is one carrier (D2), and is `some` only for an executor built metered
(`Executor.newMetered`): metering is **opt-in**, so `Executor.new` keeps its signature and the default item path
pays one `Bool` test and neither a lock nor a clock read. Busy time is measured in nanoseconds of whichever clock
the driver was given — under `Clock.live` that is `IO.monoNanosNow` (A7), under a harness clock it is virtual
nanoseconds that do not advance while work runs, so a harness run's busy time is zero by construction — so it is
printed and never asserted, the `runUs` precedent. No field is added to `Sched.State`, so `State.Aligned`'s four
preservation theorems are untouched. **Rejected: an `IO.Ref`/model field for the counters** — an `IO.Ref` read
outside a lock is D8's forbidden shape, and a model field would make the counters a second accounting the
refinement would then have to relate; the projection makes them a *consequence* of the refinement instead.

**The clock is injected and the harness drives time; the timer is not simulated away.** `Clock` is
`{ now : IO Nat, sleep : Offset → Task.Async Unit }`, and `Clock.live hooks` is the composition that existed
before it — `IO.monoNanosNow` for the reading and `awaitAsync hooks (Std.Async.sleep d)` for the wait — so the
production path is the same code, reached through a record instead of directly. `HarnessClock` is a second
implementation of the same interface, not a mock: virtual `now`, a sorted timer list under its own mutex, and
`advance : IO Bool` that sets `now` to the earliest deadline and runs that timer's fire outside the lock;
`sleep d` schedules at `now + d` and registers nothing with libuv, so no live clock is read on a harness run.
`runVirtual (hc) (e) (a)` is `runWith (e) (now := hc.now) (idle := fun _ => hc.advance)`, so the harness decides
one instant at a time and the driver parks exactly as `blockOn` does when nothing can be advanced to — which keeps
it composable with a live leaf or another thread's delivery. **Rejected: a global `IO.Ref Clock`** — unguarded
mutable configuration that makes "which clock does this run use" invisible at every call site. **Rejected:
simulating time in the model** (a `Model.Service.deadline`-style pure step) — the requirement is that the *live*
path stay the production path and the elapsed time be read from the harness, which is a runtime replacement, not a
model. **Rejected: a `sleep` that consults a flag** — it would put a branch and a shared read on the production
timer path for a test-only mode. The harness clock does not close W3's stated limit: a `withTimeout` that wins
still leaves its timer pending, unchanged.

**The signal path is W1's seam seen from the signal side.** `awaitSignal (hooks) (signum) (repeating)` wraps
`Std.Async.Signal.Waiter`: the watcher is the leaf's own (`uv_signal_start`, `runtime/uv/signal.cpp`), whose handler
resolves the promise on the libuv loop thread, and what the seam adds is that the continuation only *enqueues* —
`ctx.resume (Item.ofAction (k v))` — so the handler's step runs on the carrier, which SC17 reads as tids
(`handlerCarrier`). The boundary is the process: the fixture sends `kill -TERM` to the pid the executable publishes
in its ready marker, which is the one externally-delivered event in SC17 and the thing a fake cannot produce. The
observation is a log relation (`accept:1 < stop-observed < body-echoed < drain-returned`, `stop-observed <
offer:2`) with the affirmative control `acceptedAtStop = 1` alongside `acceptedFinal = 1` and `offered = 2`.

**The deadline arm is expressible; the policy arm is still open.** A deadline is now expressible — the clock plus
`Runtime.spawn` and `select`, exercised by SC17-O3, whose readings are `longElapsed = completesAt`,
`shortElapsed = shortDeadline` with `shortDeadline < completesAt`, `pendingAfter = 1` and `deadlineAt =
completesAt` — but `Registry`'s cancel-what-outlives-a-deadline arm and the drain-liveness argument D16 deferred
remain absent, and D18 records the trigger as met with the item open. W12's trigger ("before a server's liveness
is argued from a drain deadline") therefore stands for the *policy*, not for the instrument.

**The register and the TCB are unchanged.** New code reaches `Std.Mutex` (A1), `Std.Condvar` (A4/A5) and
`IO.monoNanosNow` (A7) — all on D7's list — plus the leaf layer's `Std.Async.Signal` externs
(`lean_uv_signal_mk`/`_next`/`_stop`, `Std/Internal/UV/Signal.lean` → `runtime/uv/signal.cpp`), which is exactly
the wholesale leaf reuse D3 names ("timers, TCP/UDP/DNS, signals, processes") and which the sockets and timers
already rely on; the one new import edge into `Std.Async` is `Std.Async.Signal` in `Leaf.lean`.
`IO.asTask … Task.Priority.dedicated` (A6) is called by the test mode, not by library code, and A6 is already
controlled by `controlDedicated`. No `IO.Promise` construction is added in the library (the test executable
constructs promises in every mode, as it always has). `#print axioms` is unchanged
because D18 adds no theorem. D7's register, the trusted-base table and its rows are untouched, and
[`proof-strategy.md`](proof-strategy.md) §2 and [`primitive-theory.md`](primitive-theory.md) §6 record the
non-change.

______________________________________________________________________

### D19 — The queue discipline at P carriers: one lock per worker, one shared inject, and the wake protocol across threads.

W8's decision record. It instantiates D4 for a *set* of workers and closes D9's trigger.

**One lock per worker's pool, one for the shared cell.** A worker's ring and LIFO slot sit behind that
worker's own `Std.Mutex`; the shared list, the parked count, the carrier count and the stopping flag sit
behind one more. That is D4 unchanged — no atomics, no lock-free deque (there are none in Lean), batch size
one — and it is what makes a worker's own queue writable by its owner alone. **The lock order is
`pool → inject`, everywhere**, and nothing takes the inject's lock and then a pool's: the only two-lock
paths are a local push whose placement overflows, and a take whose allowance has run out with the slot
occupied; both hold a pool first. A second order would be a deadlock waiting for a schedule, so it is stated
as an invariant rather than left to whichever path is read.

**The routes, and why `Item` carries an index rather than a function.** A step's re-enqueue route is not
captured once at its spawn site: the *worker that fires a step* supplies its own route, so a child follows the
worker that ran its parent (D5's interface rule "a chain stays on the core its parent ran on", now at P
carriers). The route cannot travel *in the item* as a function — a field whose type mentions `Item` in a
function-argument position is a non-positive occurrence and Lean refuses to declare the item — so
`Task.Item.act` takes the firing worker's **index** (`Nat → IO Unit`), a root is built with
`Item.ofIndexed`, and `Item.ofAction` keeps its signature and ignores the index. The worker fires with
`it.act i` and the root's closure reads that worker's route from it.

**The local route is owner-only for owner-made pushes, and there is a third off-owner site.** A push a step
makes on its own worker owes no wake — the owner is running the step that makes it — and the two *seam*
completions (`Runtime/Leaf.lean`'s leaf continuations and `Runtime/Blocking.lean`'s blocking completion) take
`Ctx.resumeShared`, the shared route, because they run on a thread that is not the owning carrier. **The audit
found two sites and there is a third, on the task layer**: `LeanIn/Task/Basic.lean`'s `Async.await` and
`select` register `ctx.resume` on a `Join` cell, and whichever carrier resolves the cell runs the continuation
— for a child delivered through the shared list, not the awaiting worker. An off-owner item therefore can land
in a worker's own queue, and with no notification that is a lost wakeup; the implementation carries a
**per-worker `poked` flag and a broadcast** (`Executor.wakeIfParked`, read and cleared only by that worker's
predicate) to make it visible under the lock order. **This is the standing mechanism at this boundary, not a
staging stand-in**: the bit's removal belongs to a *following* item that rebinds each item's `Ctx.resume` at
fire time to the firing worker's route — the shape `Item.act : Nat → IO Unit` already models for roots — and
not to this one. **Moving this site to `resumeShared` was considered and rejected**: the route on the cell is
the *awaiter's* but the continuation runs on the *resolver*, so routing it shared would send every await
continuation through the shared list and let a chain cross a carrier on a tree where nothing was stolen —
the locality the chain rows measure. Rule 2 therefore covers **two of three** sites (the two seam completions)
and leaves the third on the task layer. One new `Ctx` field, `resumeShared`, travels with the
continuation; `Ctx` has no defaults by design, so a construction site that forgets it does not compile. **The
residual convention**: a *user* who calls `ctx.resume` directly from a thread that is not the owning carrier
takes the local route into a possibly-parked owner's pool, and Lean exposes no closure environment to check a
caller's captured cell — both are facts about code this library does not own, and D9's successor below records
the narrowed promise.

**Every waiter parks through the one path, the calling-thread driver included.** `run`/`blockOn`/`runWith`/
`runVirtual` run worker `0`'s loop on the calling thread, so the driver records itself in the same `parked`
count a carrier does, in the same critical section a push tests before it notifies; there is deliberately no
second "someone is waiting" field. The driver also has a **second stop condition** and the park covers it: a
program can be completed by a carrier while its driver waits, so the completion writes the finish flag and
notifies in the inject cell's own section, and the driver's predicate reads it there. `runCarriers` — the
parallel entry — starts `p` dedicated carriers for workers `0 … p−1`, submits the root to the shared list,
and the caller **only waits** on the completion; it does not run worker `0`'s loop, because worker `0`
already has a carrier thread and a second thread on one queue is not a wider driver.

**O2's close.** `Task.Sendable`'s constructor is private to `LeanIn.Task`, so a `Sendable` exists only where
the library makes one, and the library's own marker-requiring routes (`Executor.pushInject`/`spawnLocal`/
`submitLocal`) are the ones that take one. **Compiler-enforced**: those routes, the minting at the spawn API,
and the capability boundary — `Sched.Executor`'s constructor and fields are private, verified cross-module by
`LeanIn/Test/ExecutorNarrowing.lean` (five refusal routes, each with an affirmative control), so a caller
cannot hold a carrier-side capability it did not receive. **Audit-enforced, not compiler-enforced**: the raw
transactions the routes wrap are public, because `Sendable` sits above `Sched.Executor` in the import DAG and
no module the executor can see can both mint a `Sendable` and consume it — so "every push into a carrier's
queue takes one" holds for this library's call sites by audit, and the compiler enforces it only for code that
goes through the routes. **Convention**, stated at `Runtime.spawn` and
in [`interface.md`](interface.md) §5: a caller's captured environment, because a private constructor narrows
a *type* and a closure's environment is not one. **D9's pointer** — this is the "revisit once the interface
has seen use" event, and the answer is that the marker covers the task and the capability and not the capture.

**The inject's store.** Two lists, `Data/Deque.lean`: a push conses onto the write side, a pop reads the read
side, and an exhausted read side takes the write side reversed. Not a single `List` (its O(1) end is the front,
so every append walks it — the burst cliff of [`PERFORMANCE.md`](PERFORMANCE.md) §4.3), not `Std.Queue` (a
header that calls itself temporary, and no ghost view), and the same shape `Task/Sync.lean`'s channel keeps its
buffer in. The model's `inject : List α` is the specification and keeps its `++ [x]`.

**Superseded: an index-based growable deque over `Ring`'s store.** This decision first chose that store, for
structural reuse, and called its costs O(1) amortised. That reasoning holds for a uniquely owned array, and the
inject's array never is one: the cell is reachable from every carrier, so it is marked on every store and copied
on every write, and each operation was O(depth). A backlog of 50 000 jobs took over a minute
([`PERFORMANCE.md`](PERFORMANCE.md) §4.9). The price of the two lists is that the reversal is paid in one pop,
under the lock, rather than spread out; its worst case is priced there too.

**The inject stays unbounded, and bounding its *admission* is its own item.** The inject is also the *resume*
path, so a capacity on it would make a producer either refuse a resume (a lost wakeup, exactly what
`Multi.Live` proves against) or block (which a libuv callback may not). The sound route — an admission bound
with a refusal on the external spawn entry, in `trySend`'s shape — is a public-contract change with its own
observable and is scheduled as W17 (its row in [`tokio-workplan.md`](tokio-workplan.md) §3 and its section in
§2), so this milestone measures one system and its burst rows stay comparable across the container change.

**The model at P carriers.** `Model.Scheduler` is untouched and stays the abstract single-carrier protocol;
`Model.Pool` loses its `inject` field (its `take` is slot-else-ring, its `flushSlot` is the spent-allowance
*move*, and the inject-owning layer flushes before it consults the ring, which is where SC5's ordering lives);
`Model.Inject` is the shared list; `Model.Multi` carries the composition, the transitions (`pushLocal`,
`pushShared`, `flushLocal`, `stealInto` — the thief takes one, held −1 and taken +1 with one pool lock — and
`park`), and the three obligations re-discharged: `reachable_live`, riding on **two** inductive invariants
`ZeroParked` and `InjectWatched` (the flush and a local overflow write the inject without unparking anyone, so
the per-worker invariant alone would not imply `Live`); `reachable_consistent`; and `reachable_bound`. Each
carries a breaking control with its load-bearing half named. The single-carrier statement is a corollary
through the projection `Multi.toSched`. `#print axioms` names nothing beyond `propext`/`Quot.sound`.

**The register and the TCB are unchanged.** New code reaches `Std.Mutex` (A1), `Std.Condvar` (A4/A5) and
`IO.asTask … Task.Priority.dedicated` (A6, `startCarriers` only, already controlled by `controlDedicated`),
all on D7's list; the deque is pure Lean over `Array`, which is already `Ring`'s store. No new `#[extern]`,
no extern call, no `IO.Promise` construction in library code (the blocking pool's direct reach stays the
only one). [`proof-strategy.md`](proof-strategy.md) §2 and [`primitive-theory.md`](primitive-theory.md) §6
record the non-change.

**The take path, and its measured cost.** The restructured take pays **one** pool section when its own queue
serves it, and a second (the inject) only when the pool is empty — the split's price, and the reason the
served take is the like-for-like row against the single-cell design. It also pays a **third** when the LIFO
allowance is spent with the slot occupied: the flush moves the item to the shared list and the take fetches it
back. Since nothing refreshed the allowance, that arm ran on *every* take after three (the LIFO slot is
otherwise dead for the rest of the run), which is why the take row and the chain row regressed against the
single-cell baseline. The first repair refreshed the allowance **inside every take's own transaction**
(`(Pool.tick p).takeReport`), which took that arm off the hot path but gave the allowance away: it reset on each
decision, so a chain that re-filled the slot was served without bound and the cap never bit. **D21 replaces that
repair** — the decision refreshes the allowance only when it did not serve the slot — so the spent-allowance arm
runs once per *allowance of consecutive slot polls* rather than once per take, the cap bounds a chain again, and
the extra section is not paid. The remaining gap to the D4-single-cell baseline is the split's own
per-operation overhead, and the second measurement condition is recorded in
[`PERFORMANCE.md`](PERFORMANCE.md) §3.5 as D21 leaves it — measured, with the price the bound adds stated there
rather than absorbed.

### D20 — The service driver's read bound is per read and silent on expiry; a handler's failure is answered.

**Decision.** The driver bounds each wait for request bytes and nothing else: `Config.stallTimeout` wraps
`Conn.recv` through `Runtime.withTimeout` with an injected `Clock`, so the interval between asking the socket for
bytes and bytes-or-EOF arriving on that request is bounded. The three cases the service item names — a
connection that sends nothing at all, one that stops mid-head, and one that idles between requests — are one
case: the socket gave us no byte within the bound.

**On expiry the connection ends with nothing written.** The shipped server separates a keep-alive timeout (a
silent close) from a per-head timeout (`408`); this driver carries the first and not the second. The peer has
sent nothing within the bound, so a status line would be a claim about a request that may not have arrived at
all, and one exercised outcome beats two with one untested branch.

**The cumulative per-head deadline is not carried, and the reason is the harness.** The shipped `headerTimeout`
measures elapsed time from a request's first byte, which on our carrier is a `Clock.now` subtraction; the only
way to exercise that at a stated instant is the harness clock, and under `runVirtual` the clock advances whenever
the executor's queues empty — which is exactly while our read leaf is parked — so a virtual timer always beats a
real socket read when both are outstanding. A clause whose point is "the peer's bytes arrive, and then it stalls"
would be decided by scheduling rather than by the driver. The per-read bound needs no `Clock.now` at all, which
is the second reason it is the one carried: the clock is read by `withTimeout` and by nothing else, so no clock
value reaches the machine or a response head.

**The relic reaches the scenario that came before this one.** The per-read bound wraps *every* read, so `SC19`'s
single-request scenario moved with it: its read wins the bounded race and its connection then halts, which is
why `pendingHooks` was `0` there while the read was unbounded and reads `1` now — the same losing timer,
registered until it fires with nobody waiting (it does fire later under a live clock, and the record is read
before that). Nothing of the connection is left: that scenario's `inFlightAfter = 0` with `heldBefore ≠ 0` is the
account that says so, and it is unchanged. So `SC19`'s assertion set is narrowed **with this paragraph as its
record**: `pendingHooks` is bound by its own named field — the record's shape still requires it — and compared
nowhere, and its section's prose is corrected with it. The detector that scenario and the stalled clause share is
narrowed once for both, for this reason rather than as a patch to a frozen scenario, and every other
`pendingHooks` reading in the tree (`docs/tokio-workplan.md`'s `SC10` and `SC17` evidence lines,
`docs/proof-strategy.md`'s conservation claim for `SC10`) is re-read against the current records and left with its
reason or narrowed the same way.

**A handler's failure is answered, not re-raised.** A handler that returns `error` gets the machine's own
`closeWithError .internalServerError` — `500` with `Connection: close` and `Content-Length: 0` — and the caught
`IO.Error` is dropped. The accept loops discard per-connection results (`Registry.joinAll` awaits with
`let _ ← Async.await h`), and the shipped `onFailure` notification has no carrier in a plain-function handler, so
re-raising would cost the loop a failure channel nothing reads; the response the peer gets is the observable.

**A transport failure is not a handler failure.** The streaming body reader and response writer classify a
failed read, a stall, a truncated or closed body, and a send that cannot reach the peer on a separate VM abort
channel (D23): it passes `VM.attempt` and every middleware, so no further response is attempted — the driver
closes the connection and reports it as a transport error, and bytes already sent are not retracted.
`catchErrors` classifies no error by its message text; an ordinary error whose text begins `Http:` is answered
with the usual 500 and its `toString` body.

**What remains open, and its limits.** (i) A peer that sends one byte before each deadline keeps a connection
alive indefinitely: the total time to a complete head is unbounded. (ii) The bound is on reads, not on a handler
or on `accept`: a handler that never returns is unbounded — cancellation is W5's and W7's item — and the accept
leaf belongs to the accept loop. D23's abort covers only the peer's own I/O failure, not an arbitrary parked
handler. (iii) `withTimeout` cancels the `Task.Async` computation when the deadline wins, and it leaves a relic
on **either** side. The cancellation stops that computation's own steps: the deadline's fire sets its token, so a
step the loser had queued is skipped at `Item.fire` rather than run. It is **not** a withdrawal of an
already-submitted raw read or write, and it does not preempt an operation already executing on a blocking or
foreign thread: those finish, and the race's first writer still stands because both arms resolve through
`Join.resolveFirst`. When the read wins, the timer stays pending until it fires with nobody waiting: one timer
registration per read that won, which the SC20 records read as `pendingHooks` 3 in the keep-alive clause (its two
request reads and the end-of-stream read), 1 in the failure clause (its single request read), and 0 in the
stalled clause, whose read lost. When the **timer** wins, the losing read arm is left as its own queued step —
one held item, identified by that arm's cancel token, appearing as that arm's socket registration finishes after
the run returns, and consumed by the next drive, which takes the count from 1 to 0 with no timer, no
registration and no second step. That token is set by the time the item is taken, so firing it runs nothing and
the `resolveFirst` it would have made is never reached; the item's presence is the relic, not work. It is the
race's loss and not connection work: nothing the connection owed is
left unrun. **Because both are the race's relics and not this driver's behaviour, no scenario asserts a leftover
count**: `pendingHooks` is printed in all three SC20 records and asserted in none; `inFlightAfter == 0` is
asserted in the two clauses whose read won, and in the stalled clause after the drive that consumes the losing
arm; and `pendingAfter == 0` is asserted only where the timer itself resolved the read. Removing the timer's
wheel entry rather than letting it fire inert is the timer machinery's own remainder
([`tokio-workplan.md`](tokio-workplan.md)'s W3 debt), not this driver's; cancelling the losing computation is
`Runtime/Time.lean`'s and is done there (`tests/timeout-cancel-contract.md` TC1).
(iv) A failed *socket* operation still ends the connection past
`Conn.shutdown`; the handler-failure path no longer reaches that short-circuit, because the failure is answered
inside the loop. On the streaming path a failed send is now an abort (D23) too, and it closes the connection the
same way — the difference is that no 500 is attempted first, because the transport cannot be relied on to carry
it — while bytes already written (a started head, earlier chunks, or the prefix the failed send delivered) stand
and are not retracted.

**Evidence.** SC20 (`nix develop -c bash tests/executor-contract.sh SC20`): the stalled peer's clause asserts the
harness clock's own stated instant (`at == stall` with `stall = 30`, `clientGot` empty and `bounded == no`), and
the failure clause binds the client's bytes to the derived `500` literal. The relics above are read rather than
asserted: `pendingHooks` prints 3 / 1 / 0 across the three clauses — one timer per read that won, and none where
the read lost — and the stalled
clause's `inFlightAfter` is read after the drive that consumes the losing read arm — so both relics' identity is
in the record without either becoming a claim about `withTimeout`.

______________________________________________________________________

### D21 — The LIFO allowance bounds consecutive slot polls, and the take's own decision refreshes it.

**Decision.** A carrier's take refreshes the allowance **unless the slot served it**: `Pool.takeReport`'s returned
pool carries `lifoPolls := p.lifoPolls + 1` on a `.slot` decision and `lifoPolls := 0` on `.flushed` and `.queue`,
so the allowance counts **consecutive slot polls** and the cap bounds a chain rather than a run. The refresh sits
in the decision rather than at a call site because `Pool.takeReport` is the one function both take spellings call
— the carrier's (`Executor.takeFor`) and the driver's record path (`Executor.takeReport`) — and the one place
that knows which way the take went, so the two cannot disagree about the allowance. `Pool.tick` still means "the
allowance refreshes", `Executor.tickFor`/`tick` are unchanged, and the three laws beside the count companions
state the decision's own behaviour: `takeReport_lifoPolls` (the law above), `takeReport_flushes_when_spent` (a
spent allowance with the slot occupied clears it for the shared inject and reports the occupant as the decision
observed it) and `takeReport_bounded`.

**What it restores, and what it does not promise.** `interface.md` §5's allowance is now what it says: per
carrier, bounding *consecutive* slot polls, with a spent allowance's occupant flushed rather than stranded — so a
chain that keeps the slot occupied cannot keep the ring from being served, and a chain that yields (a spawn/await
round trip) is not demoted. The model is untouched, and that is the point: `Model.Pool.take` is the decision and
`Model.Pool.tick` the refresh, the transition relation admits a tick at any point, and `reachable_bound` is an
invariant over states — this decision fixes the *schedule* of the refresh, not the invariant. Nothing here
promises that a task runs: §5's no-fairness bullet and A6 stand, and what is bounded is a sequence of decisions,
not a step's duration or a wait.

**The two shapes rejected.** (i) **No refresh at all** — the take never ticking, the state before `9a8386f`: the
allowance accumulated against the whole run, the slot was dead after three polls, and the spent-allowance arm ran
on every later take, moving an item to the shared list and fetching it back. D19's take-path paragraph records
that regression. (ii) **Refresh on every take** — D19's first repair, `(Pool.tick p).takeReport`: the allowance
reset on each decision, so a chain that re-filled the slot was served forever, the cap never bit, and a carrier
could not reach its own ring; SC12 is the scenario that reads it, and this decision replaces that repair rather
than adding to it.

**What it costs, and the condition it misses.** The round trip against the take-refresh removal (the shape before
`9a8386f`, a scratch export outside the repository) is **2346 ns against 2510** and, on `spawn+take`, **435 ns
against 705** — the interleaved run that stands; an earlier session read 3114 against 4149 and 709 against 1249,
and its raw log is no longer on disk, so those figures are quoted as reported rather than re-inspectable. Against
the immediately preceding tree the price is real and paid deliberately: `--runtime-ops` reads it above that tree
(+27% round trip, +31% `spawn+take`), and the chain row's ratio falls from the base's same-session **9.00–11.26**
to **8.07–8.52**, both at `chainCarriers = 1`, with the flush counts over a 2000-link chain reading **1001**
against **1** (and **3997** for the take-refresh removal) — one flush per two links, because a spawn/await link's
continuation takes the same slot route as its spawn. **W8's second measurement condition, read as its definition
reads, is therefore not met**, and it is recorded here rather than re-baselined: what survives is the advantage
over the native pool (8.07–8.52 against the same session's native row, nowhere near the native band), and the
chain row's ratio against the take-refresh removal is **unmeasured** — the session's third arm was byte-identical
to the second, so no figure is claimed for it. The three levers a reader might reach for are each their own
item, and this record takes none of them: raising the cap weakens the bound; bounding by *steps* rather than
decisions is a different policy; and D19's route question — rebinding each item's route at fire time — would take
an await continuation off the slot, at the cost this record's chain row now measures.

**Evidence.** SC21, whose expectation is derived from the model and the schedule above, reads field for field the
derived decision sequence (`slot, slot, slot, flushed, queue, slot, slot, slot, flushed, slot, slot, slot,
flushed`, three flushes); SC5 is byte-identical, which is the guard that the explicit tick still refreshes; SC12
is green where it read the cap's absence; the two take spellings read one transaction; `LeanIn/Model` is
untouched; and the three laws' `#print axioms` lines name nothing beyond `propext`/`Quot.sound`.

______________________________________________________________________

### D22 — A step's re-enqueue takes the firing worker's route, and a deferred continuation is an item on the resolver's own queue.

W18's decision record, and **D19's residual closed**: the per-worker wake flag and its broadcast are gone,
because the third off-owner local push they covered no longer exists.

**The route is read at fire time, never captured.** D19 had the route travel as an *index* (`Item.act : Nat →
IO Unit`) and a root supply the firing worker's route. This decision makes that the *only* way a route enters a
step: `Task.Ctx` carries the worker's own route (`resume`) **and the runtime's route table** (`routeAt`, whose
`n`-th entry is worker `n`'s own queue), a step's own re-enqueue reads the table at the index it is fired with
(`Ctx.rebind`), and a continuation that a *different* worker resolves is delivered as an item —
`Task.Item.ofDeferred` — whose action re-binds the waiting computation's context at the firing index. So a
step's re-enqueue takes the route of the worker that fires it, and **no continuation holds a route that was
resolved before it ran**. The rule's other half is its mirror: every resume that is *not* a step's own
re-enqueue — a leaf completion, a blocking completion, the harness clock's fire, a resolution made by a thread
that owns no queue — takes the **shared** route (`Ctx.resumeShared`), whose push appends to the inject and
unparks a parked waiter inside that same section.

**The census, because the last three counts in this family were wrong.** D19's own audit found two off-owner
sites where the code has three, and this milestone's first draft then named one continuation registration where
the repository has five. Each site is therefore written out, with its route and its owner before and after; the
table is in `LeanIn/Task/Basic.lean`'s module header. The five registrations a *resolving step* runs
(`Async.await`, `select`'s final continuation, and `Semaphore.acquireStep`/`Channel.sendStep`/`Channel.recvStep`)
now deliver on the **resolving** worker's own queue, and the harness clock's fire takes the shared route. The
distinction the `Sync` sites turn on is preserved: **the route comes from the firer and the token from the
waiter** (`Item.ofDeferred` carries the waiter's token and ambient context), so a retry keeps its own stamp.

**Why the resolver's *own* queue, and the shared route rejected for that site.** A `Join`-cell continuation is
delivered as an item on the route of the worker that resolves the cell, because the resolver *is* a carrier: the
thread that pushes and the worker that owns the target queue are the same worker, which is exactly `pushLocal`'s
premise. Routing the site through `resumeShared` — D19's rejected alternative, restated here because it stays
rejected — would send *every* await continuation through the inject and let a chain cross a carrier on a tree
where nothing was stolen, and it would put that traffic on the one contended cell W8's third milestone prices.
`Join.onReady`'s "already resolved" case keeps calling the continuation inline: that is the *same* worker's
step, so nothing is deferred and no route is needed.

**What is removed.** `Executor.wakeIfParked` and its two callers, the per-worker flag it recorded and the
helper that set it, and the two predicates' reads of that flag. With them goes the shared section every local
push paid for it (`submitLocalRaw`/`spawnLocalRaw` now make one pool transaction; their placement overflow
still unparks through `pushItems`, as every shared push does). With the third off-owner site gone, `pushLocal`'s
"worker `i` is not parked" holds as an implementation fact rather than a convention a wake has to repair, and
`Model/` is untouched: this is the implementation moving back onto the premise the model already had.

**The locality's identity changes, and which construction each row prices is now written down.** A chain link is
pushed on the route of the worker that *resolved* it — the worker that ran the child — so a chain follows the
worker that fires each link, and `chainCarriers > 1` is legitimate rather than a defect. The old reading
(`chainCarriers = 1`) meant "the chain did not leave the core its parent ran on **because the parent's route was
captured**"; the new reading is the interface's own rule, now stated in `interface.md` §3, where a chain stays
on the core its parent *ran* on. W8's LIFO milestone criterion 2 (`chainCarriers = 1` on *that* milestone's
arm, whose chain is spawned through `Handle.spawn` on `p` carriers) is re-read as the pre-rebinding identity,
and its criterion 3 — the ratio against the base revision — is a different construction and is not re-used.

**What it costs and what it buys, measured.** The change's only cost on the local path is that a
`Push`-carrying operation states its route: `Join.resolve`/`Join.resolveFirst`/`Task.cancel`/`Runtime.cancel`
and the `Sync` operations that deliver waiters take the *delivering step's* own route — `Task.Async.push`, read
in the step that makes the call, never hoisted across an await, because a route fetched earlier is a route of a
worker the calling step may not be running on. What it buys is the enqueue side W8 gave back: interleaved
against the base revision in one session (four runs an arm, minima per §1, 8 cores, kernel 6.17.0-1032-oem, load
2.6–3.3), `Executor.spawn` reads **331 ns with the flag against 287 without it** — 44 ns in the same session, in
the direction W8's record stated (466 against 372–389) — and the `spawn+await` round trip is not regressed by
delivering a continuation as an item (base min 1906 ns against 1850). `docs/PERFORMANCE.md` §3.5 carries the
runs, the interleaving and the load.

**Evidence.** SC22 is green and reads the *mirror* of the route clause's unstaged red: the pre-fix tree read
`creatorPoolAfter=1|firerPoolAfter=0|continuationTid=creatorTid` for a chain crossing carriers, and the fixed
tree reads the firing worker's own pool gaining one, the creator's unchanged, the shared list empty, and the
firing worker's thread running the continuation. The staged cut no longer matters — with a `wakeIfParked` whose
entire action is `pure ()`, called from both local pushes, re-applied in a scratch copy, SC22's completion
clause reads `completed=1|crossed=1|waiterParked=1|heldAfterStop=0`, where the same cut on the pre-fix tree
read `completed=0|waiterParked=1`. The no-regression set is SC1–SC3, SC5, SC12–SC14 and SC16–SC21; the four
scenarios coupled to the changed sites are SC13 (the sync registrations), SC14 (the service's admission bound),
SC16 (`select`) and SC12 (the blocking seam). `Model/` is byte-identical.

**What this does not establish.** (i) It does not show that *no other* site needed the flag: that is the
census's job, and the census is held to the standard of naming every site that can enqueue into a worker's own
queue, with the shared-by-design ones named and given their reason. (ii) The harness clock's fire takes the
shared route even though today's only advancer is the single-carrier driver: pushing on the sleeper's local
route is owner-made only under that caller's convention, and a convention cannot be load-bearing once the flag
is gone — a `clock` advanced from another thread would push into a parked worker's own queue with nothing to
wake it. (iii) The `Sync` primitives' delivering operations now take a route, which is a signature change for
`Semaphore.release`, `Mutex.unlock`, `Channel.trySend` and `Channel.tryRecv`: they stay `IO` (the interface's
parking/non-parking split is untouched) and their callers state the route.

______________________________________________________________________

### D23 — A request's transport cancellation is a typed VM abort, not a catchable error and not `Task.Cancel`.

**What it is.** The streaming HTTP driver gives a request its own cancellation channel in
[`LeanIn/Runtime/VM.lean`](../LeanIn/Runtime/VM.lean). `abortE` raises an abort, `tryAbortE` is the only thing
that catches one, `Outcome` tags how a scoped machine ended, and `VM.requestScope` runs a handler machine to
exactly one of value, ordinary error or transport abort. `VM.abortOnFailure` wraps **one** raw completion so that
that completion's own failure — a read error, a stalled or truncated read, a send that cannot reach the peer —
is delivered to the abort channel. Because the classification lives in the leaf, a `do` block's later steps keep
the ordinary error channel: an application `throw` after a successful send is an application error, never an
abort. That property was the reason for the shape: an earlier encoding, a node whose interpreter converted the
error channel of an enclosed subtree, also converted every later step of a `bind` and was rejected for it.

**Where the driver puts the scopes.** [`LeanIn/Http/Server.lean`](../LeanIn/Http/Server.lean)'s
`driveStream` wraps the handler in `VM.requestScope` and puts the body reader's five read sites (raw read
failure, stall, peer close, in fixed-length and chunked framing alike) and the response writer's head, body-chunk
and terminating-chunk sends on the abort channel. On `.aborted` the driver closes the connection and reports
`onClose (.error reason)`, attempting no further response — no 500, no keep-alive. It does not claim zero bytes: a
response head or body written before the failure, or the prefix a failed send delivered, cannot be retracted.
HC1's zero **post-close** bytes are the pre-response body-read case, where no response byte had been written yet.
`catchErrors` no longer classifies by message text; it answers ordinary errors, including one whose `toString`
begins `Http:`, with a 500 whose body is that `toString`.

**Why not `Task.Cancel`.** Its gate is `Item.fire`, which skips a cancelled computation's step (D14, W5), and
its token is `IO.Ref`-backed with an explicit cross-carrier caveat (D14). Request cancellation here is raised by
the operation that observed the failure, in the step that observed it, and travels as a machine value: no token,
no second carrier, no cross-thread flag.

**What it does not claim.** (i) Only the **peer's own I/O** cancels a request. There is no user-triggered
cancellation of an arbitrary parked handler, no child-request or blocking-job cancellation, and no
shutdown/drain; P7 stays open in its own right and D20's unbounded-handler limit is unchanged. (ii) The
**buffered** entrypoint `drive`/`serveConn` gets no scope: it exposes no streaming reader or writer, and an
explicit `VM.abort` in one of its handlers has no catch — `run`/`runToCell` route an uncaught abort to `throw`,
loudly, where the machine resumes. (iii) The primitive register and the bridge axioms are unchanged: no new
extern, `IO.Promise`, atomic, syscall, axiom or theorem, and no new import edge into `Std` (audited by direct
calls and import edges, not by text search); `docs/primitive-theory.md` §6 records it. (iv) The correspondence
between "the abort reached the operation" and "the compiled driver's await completed, closed the connection and
reported a transport error" is **tested, not proved**: HC1 at the public socket
(`tests/http-cancel-contract.md`), the focused VM controls in `LeanIn/Test/Control.lean`, and the callsite audit
of `Stream.responseWriter`. It is not a discharge of P7 or P8 ([`proof-strategy.md`](proof-strategy.md) §2, §5).

### D24 — `Std.Http`'s request, response and handler hooks are a layer on the streaming driver, not a second driver.

**What it is.** [`LeanIn/Http/StdHandler.lean`](../LeanIn/Http/StdHandler.lean) defines `StdHandler`: a handler
from `Std.Http.Request Server.BodyReader` to `VM (Std.Http.Response ResponseBody)`, with `Std.Http.Server.Handler`'s
`onFailure` and `onContinue`. `StdHandler.toStream` converts one to a `StreamHandler`, and `Server.serveConnStd`
serves it through `serveConnStream`. Libraries written against `Std.Http.Server`'s request and response types
(routing, middleware, authentication, the Lambda host) then need only to be polymorphic over the monad and the body
types to run on LeanIn ([scidonia/leanin#1](https://github.com/scidonia/leanin/issues/1)).

**Why a layer.** The H1 machine and the native `StreamHandler`/`BodyReader`/`ResponseWriter` path stay as they are,
so the stock `Headers` map and the parsed `RequestTarget` are built only for a handler that is a `StdHandler`. Whether
this becomes the only public handler shape is a separate decision, to be taken on measurements of that per-request
cost.

**The contracts, each matched to `Std.Http.Server`.**

- **Request.** `Request.Head` carries the method, version, `uri` and a validated `Headers`; `extensions` carries
  `Std.Http.Server.RemoteAddr`, read from `BodyReader.peer`. A head `Std` rejects (a header name or value that is
  not a valid token, a target `RequestTarget.parse?` refuses) answers `400` without running the handler.
- **`onContinue`.** Asked for an HTTP/1.1 request with `Expect: 100-continue`. `true` sends `100 Continue`; `false`
  or a raise answers `417 Expectation Failed` without running the handler, and the connection closes unless the
  request had no body to wait for. `serveConnStd` requires `continuePolicy := .application` and raises when it is
  not, so the decision is the
  layer's.
- **`onFailure`.** A notification, called for an error the handler raises, a rejected head, and a transport abort.
  `Std`'s connection loop calls it for the first two as well as for transport errors, so the layer does too; a
  handler then behaves the same on either host. The failure takes its usual course afterwards (a raise is the
  driver's `500` when no response has started; an abort closes the connection), and an error `onFailure` raises
  itself is discarded.
- **Response.** `ResponseBody` is a LeanIn type: `bytes`, or `stream` with an optional length and a writer handed
  a chunk sink. It is not a class and not a `Std.Http.Body` instance: the shared libraries own their body
  abstraction and give this type an instance of it, and a `Std.Http.Body` would bring `Std.Async` into the serving
  path. A declared length is enforced: a producer that writes past it, or finishes short of it, fails the
  connection rather than emitting a malformed body. Trailers are not supported: neither `ResponseBody` nor the
  native `ResponseWriter` has a trailer channel, so a handler that needs them must not claim chunked trailers.
- **`Date`.** Added as an IMF-fixdate when the response has none, as `Std.Http.Server` does by default
  (`Config.generateDate`, default `true`). It is formatted from `Std.Time.Timestamp.now` at most once a second,
  with no time zone database.

**Evidence.** `tests/std-handler-contract.md`: SH1 (head, repeated headers, `RemoteAddr`, `Date`), SH2 (`417`,
close, handler not run), SH3 (`onFailure` once for a raise and once for a mid-body disconnect, never for a clean
request) and SH4 (`400`, handler not run). All four were run against the conversion without these contracts first
and failed on their own assertions; `tests/std-date.sh` checks the date formatter at fixed instants.

**What it does not claim.** (i) **Not every `onFailure` site `Std` has.** A stall before a head arrives (`Std`
answers `408`), a head the H1 machine itself rejects, and a send failure outside the request's scope are the
driver's and are not reported; reporting them means a hook in `driveStream`. (ii) **`Compat.ofStock` is
unchanged** and does not consult the stock handler's hooks: the buffered driver has sent any `100 Continue` and
read the body before the handler runs. (iii) **The layer costs throughput**: about a microsecond per header, and
the layer serves 81–89 % of the native keep-alive throughput on a two-header request
([`PERFORMANCE.md`](PERFORMANCE.md)), so it stays an opt-in and is not the only public handler shape. (iv) The
primitive register is unchanged except for one direct external operation in the HTTP layer,
`Std.Time.Timestamp.now`, reached for the `Date` value; the module's only new import
edge into `Std` is `Std.Http.Server` (for `RemoteAddr`), which `Compat` already had. (v) A trace test; it can
falsify these contracts and cannot establish them for requests it does not send.

______________________________________________________________________

## Open

No decision is open: D19's residual is closed by D22, and D24 is this register's last entry. The limits those
records leave open — the uncarried cumulative head deadline, the trickling peer, `withTimeout`'s inert wheel
entry when its computation wins and the skipped step it leaves queued when its deadline wins, the second
measurement condition as D21 reads it, the harness clock's single-advancer convention as D22 reads it, D23's
request scope limited to peer I/O on the streaming path, and the `onFailure` sites D24 leaves to the driver — are
stated in their own entries rather than here.
