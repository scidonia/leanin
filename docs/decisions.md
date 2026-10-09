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

**Deliberately excluded.** Atomics (not exposed). `IO.Promise` (Mutex+Condvar covers it, so it stays
out of the TCB). Thread creation (v1 runs on the caller's thread; D2). `IO.Ref` — see O1.

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

**Note on A6.** M4 needs threads, but they come from `Task.Priority.dedicated` — i.e. from `Task`,
which D3 already places in the TCB. So A6 as a raw `pthread_create` axiom is *still* not needed in v1.
That holds only as long as the blocking pool is built on `Task` rather than spawning threads itself;
if it ever spawns its own, A6 joins v1's axiom set.

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
*replace* the pool can do this: a site that restores the pool it read cannot, because the in-place mutation
moved the value it means to restore — which is why a refused take still pays the copy.
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

## Open

None. All decisions are closed; D9 should be revisited once the interface has seen use.
