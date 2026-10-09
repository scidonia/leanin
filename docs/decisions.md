# Decisions

Settled decisions and the evidence each rests on. Evidence anchors are in
[`lean-scheduler.md`](lean-scheduler.md) (the current runtime), [`tokio-map.md`](tokio-map.md) (what
we are taking) and [`evidence.md`](evidence.md) (measurements). Two decisions are still open; they are
at the bottom and nothing downstream should be treated as fixed until they close.

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
See M2b in [`PLAN.md`](../PLAN.md).

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
queue short. There is no bound on the backlog: bounding it with back-pressure is a separate item — W6 built the
mechanism such an item would use, a semaphore with a capacity (D14), but back-pressuring `submit` changes its
signature and SC12's accounting and needs its own scenario, so it is named rather than silently taken. A submit to a stopping pool **throws**
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

______________________________________________________________________

## Open

None. All decisions are closed; D9 should be revisited once the interface has seen use.
