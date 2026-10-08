# Tokio: what we are stealing, and from where

Reference copy: `Vendor/tokio/`, cloned from `github.com/tokio-rs/tokio` at
`3eb95a40f1b88623470c4e902e2fa90e807fdeed` (`master`, 2026-10-07). Latest release at the time of
writing is `tokio-1.53.2` (2026-10-04). All line anchors below are into that checkout, so every claim
here is checkable with `rg` rather than remembered. Tokio is MIT-licensed; the copy is read-only and
outside our build (`.gitignore`d).

A caution that shaped this document: **the commonly repeated claim that Tokio's queue is a Chase–Lev
deque is wrong.** Tokio's own account is in "Making the Tokio scheduler 10x faster" (2019-10-13,
`tokio.rs/blog/2019-10-scheduler`, PR `tokio#1657`): Tokio 0.1 used crossbeam's deque, "based on the
Chase-Lev deque, which … is not a good fit"; the rewrite replaced it with a queue adapted from the
**Go runtime**. The reason is concrete: Chase–Lev grows dynamically, growth needs epoch-based
reclamation, and reclamation costs two atomic RMWs on every operation in the hot path. Tokio traded
growth for a **fixed-size local queue that overflows into a shared queue**.

______________________________________________________________________

## 1. Scheduler flavours

| Flavour | Path | Shape |
|---|---|---|
| multi-thread, work-stealing | `tokio/src/runtime/scheduler/multi_thread/` | *P* workers, per-worker local queue, global inject queue, stealing |
| current-thread | `tokio/src/runtime/scheduler/current_thread/mod.rs` (925 ln) | one task at a time, no stealing, no thread-safety requirement |
| blocking pool | `tokio/src/runtime/blocking/` | separate pool, separate queue, *not* work-stealing |
| `block_in_place` | `tokio/src/runtime/scheduler/block_in_place.rs` | hands the worker's core to another worker, runs blocking on this thread |
| `defer` | `tokio/src/runtime/scheduler/defer.rs` | deferred wakeups within a tick |

Porting note: the multi-thread flavour is the project; `current_thread` is the same code minus the
stealing and is a good second target because it is drastically simpler to prove.

## 2. The local run queue — the heart of it

`scheduler/multi_thread/queue.rs` (602 ln). `LOCAL_QUEUE_CAPACITY = 256` (line ~66; **4** under
`loom`, so the model checker can reach the interesting interleavings — a testing technique worth
copying).

```
struct Inner<T> {
    head: AtomicUnsignedLong,   // packed: [steal ticket : UnsignedShort][real head : UnsignedShort]
    tail: AtomicUnsignedShort,  // only written by the producer, read by everyone
    buffer: Box<[UnsafeCell<MaybeUninit<Notified<T>>>; LOCAL_QUEUE_CAPACITY]>,
}
```

The `head` packing is the interesting part, and the source comment (line ~38) explains it exactly:

> **"Use wider integers when possible to increase ABA resilience. See issue #5041."** … The `MSB` is
> set by a stealer in process of stealing values. It represents the first value being stolen in the
> batch. … **"Tracking an in-progress stealer prevents a wrapping scenario."**

So the queue is **not** Chase–Lev: there is no `top` CAS race on a single slot, and no tag field. It
is Go's `runqgrab` design — a *ticket* in the high bits of `head` that marks "a steal is in flight",
which simultaneously (a) makes a second concurrent stealer bail out, (b) makes the producer's
full/empty check conservative rather than wrong, and (c) mitigates ABA. Three properties from one
trick.

Operations:

- **`push`** — producer only: `head.load(Acquire)`, `tail.unsync_load()`, write the slot, `tail.store(Release)`.
  No RMW, no `seq_cst` in the fast path. The blog's own analysis: on x86 this is *zero*
  synchronisation instructions.
- **`pop`** — owner only: load, read slot, then **CAS `head`**, because a concurrent stealer may have
  claimed it. The CAS is the linearization point.
- **`steal_into` / `steal_into2`** — a thief steals **into its own queue**, in a **batch of half the
  capacity** (`LOCAL_QUEUE_CAPACITY / 2` guard at line ~431), and **aborts** if another stealer is
  already in flight (`src_head_steal != src_head_real`, line ~482). Batching is deliberate: it
  amortises the CAS and reduces the number of steal attempts. It also means steal is *not* a
  one-element operation, which is exactly the kind of thing that breaks a naive linearizability spec.

Porting note: this is the single highest-value and highest-risk component to port. It is ~600 lines
of very carefully ordered atomics with a documented reason behind every one. **Its `steal_into`
batching and in-flight ticket are what make the proofs hard** — and they are also what make it fast.

## 3. Inject queue (the global queue)

`scheduler/inject.rs` + `scheduler/inject/{shared,synced,pop,rt_multi_thread,metrics}.rs` (~613 ln
total). Described in the source as *"Growable, MPMC queue used to inject new tasks into the scheduler
and as an overflow queue when the local, fixed-size, array queue overflows."*

Note the 2019 blog calls it "an intrusive linked list guarded by a mutex"; the current source is far
more refined — a batched design split into a lock-free `shared` half and a mutex-guarded `synced` half
with a dedicated `pop` path, plus a separate multi-thread-facing `InjectQueue`. **Read the current
source, not the blog, for this component.**

Two consumers: (i) `Local::push` overflow, which moves **half** the local queue out (again batching,
so the "queue looked full but wasn't" false positive is rare); (ii) any non-worker thread calling
`spawn`, which is the `Send`-able entry point.

`overflow.rs` (26 ln) is the small adapter between the two.

## 4. The LIFO slot — Tokio's message-passing optimisation

`worker.rs:120–126`:

```
/// next (LIFO). This is an optimization for improving locality which
lifo_slot: Option<Notified>,
/// When `true`, locally scheduled tasks go to the LIFO slot. …
lifo_enabled: bool,
```

with `MAX_LIFO_POLLS_PER_TICK = 3` (`worker.rs:265`, comment: *"Value picked out of thin-air. Running
the LIFO slot a handful of times …"*) and a runtime knob `config.disable_lifo_slot`.

The idea: when task A wakes task B (a message send), B goes into A's LIFO slot and runs next, so the
message pass stays on the same core and the cache line stays hot. The bound of 3 polls per tick exists
so the slot cannot starve the local queue. On a core steal, the LIFO slot is *not* stealable, so
`worker.rs:479` moves it back into the run queue first.

Porting note: cheap to implement, hard to justify in a proof (it is a *performance* heuristic with no
correctness role). Good candidate for "implement and test, do not prove".

## 5. Coop budget

`runtime/coop.rs` (not in `scheduler/`). Every task gets a budget; when it is exhausted the task
yields back to the scheduler (`coop::has_budget_remaining()`, `worker.rs:736`). This is what stops one
CPU-bound task from starving its worker's queue — the cooperative answer to the problem a *preemptive*
runtime solves with preemption.

Porting note: Lean has `IO.checkCanceled` and a heartbeat mechanism (`IO.getNumHeartbeats`,
`IO.setNumHeartbeats`), and `IO.setTaskPriority`. A budget is implementable, but it must be checked
*cooperatively* by user code, which is a semantic difference from Tokio (where the scheduler owns
`poll`).

## 6. Park / unpark and the idle protocol

`scheduler/multi_thread/park.rs` (316 ln) and `idle.rs` (248 ln).

The `Parker`/`Unparker` pair holds `state: AtomicUsize`, a `Mutex<()>`, a `Condvar`, and an
`Arc<Shared>` for the resource driver. `HadDriver { Yes, No }` records *why* a worker parked, so that
a worker parked on the I/O driver is not woken by a mere spawn but a worker parked with the driver
enabled can be.

`idle.rs` maintains the set of sleeping workers so that a task pushed into the inject queue can wake
**one** of them rather than all. That is the "sleep fewer, wake one" discipline the blog describes
under "throttle stealing".

Porting note: this is where Lean's missing `Task`-level waker bites. Tokio's `Waker` is a two-word
`RawWaker` whose vtable pushes the task onto the right queue; Lean has only `IO.Promise`
(one-shot, `resolve`-orphan returns `none`) and a task's continuation. **Waking a parked `leanin`
worker must therefore be built out of `Promise`/`Condvar`/`Task.spawn` and then *proved*** — this is
`docs/proof-strategy.md` T6, and it is the first thing M3 must solve.

## 7. Drivers

| Driver | Path | Mechanism |
|---|---|---|
| I/O | `runtime/io/driver.rs`, `runtime/io/driver/{uring,signal}.rs` | `mio` (epoll/kqueue/iocp) by default; **io_uring** behind the unstable `io-uring` feature (`tokio/Cargo.toml:88`, requires `--cfg tokio_unstable`) |
| time | `runtime/time/wheel/` (~830 ln) | **hashed hierarchical timing wheel** (`wheel/mod.rs`, `wheel/level.rs`), sharing the I/O driver's poll for wakeups |
| process, signal | `runtime/process.rs`, `runtime/signal/` | `mio`/`signal-hook`-style |
| generic op abstraction | `runtime/driver/op.rs` | unifies blocking and io_uring operations behind one interface |

Porting note: **out of scope.** Lean already has a working libuv driver, and it is measured to be
non-blocking (64 concurrent `Async.sleep` in 102 ms **[M]**). Replacing it would be a second project
with none of the proof interest. We compare against it, we do not reimplement it.

## 8. Task lifecycle

`runtime/task/` (≈2 700 ln): `raw.rs` (378) — refcounting and the ref/ref_owner/drop state machine;
`state.rs` (657) — the task state machine (running / scheduled / complete / cancelled); `core.rs`
(593) — the `Cell` shared between `JoinHandle`, `Waker` and the scheduler; `waker.rs` (124) — the
`RawWaker` vtable; `join.rs` (377) — `JoinHandle`; `abort.rs` (105) — cancellation; `harness.rs` (569)
— the `Harness` wrapping a future in a task; `list.rs` (368) — the intrusive list used to move batches
of tasks with one atomic.

Porting note: `state.rs` is the piece worth *proving* — it is a small, self-contained concurrent state
machine, and it is exactly the kind of object Iris is good at. Most of the rest is an allocation and
reference-counting optimisation and should be implemented straightforwardly, not proved.

## 9. Blocking pool

`runtime/blocking/`: `pool.rs` (780 ln) + `sharded.rs` (353) — a sharded, per-core idle queue;
`schedule.rs`, `task.rs`, `shutdown.rs`, plus a slab allocator. Separate from the async pool, spawned
by `spawn_blocking`, and **not** work-stealing.

Porting note: this is the component that fixes our measured pathology (64 × `IO.sleep 100` → 801 ms
because blocking work occupies an async worker **[M]**). Comparable in importance to the scheduler
itself, and far simpler. **Do this early** — it is the cheapest large win in the whole plan.

## 10. Synchronisation primitives

`tokio/src/sync/` — `Mutex`, `RwLock`, `Notify`, `Semaphore`, `oneshot`, `mpsc`, `broadcast`,
`watch`, `OnceCell`. Each registers its waiter with the waker machinery rather than blocking a thread.

Porting note: **Lean already has equivalents** (`Std.Sync`), so this is a comparison, not a port. The
interesting difference is that Lean's `Mutex` is a real blocking OS mutex (C++), whereas Tokio's is an
async-aware lock; and Lean's channels are built on `Mutex` + `Promise` rather than on wakers.

______________________________________________________________________

## What we steal, in priority order

| # | Component | Tokio path | Size | Port cost | Proof interest |
|---|---|---|---|---|---|
| 1 | **blocking pool** | `runtime/blocking/` | ~1 300 ln | low | low (mechanism is easy; the *policy* is what needs care) |
| 2 | **inject queue + overflow** | `scheduler/inject*`, `overflow.rs` | ~640 ln | medium | **high** — batched MPMC, linearizability |
| 3 | **local run queue** | `multi_thread/queue.rs` | 602 ln | high | **highest** — in-flight ticket, batched steal |
| 4 | park / unpark / idle set | `park.rs`, `idle.rs` | 564 ln | high (no Lean waker) | **highest** — P6 no-lost-wakeup |
| 5 | worker loop, core ownership | `multi_thread/worker.rs` | 1 566 ln | medium | medium |
| 6 | task state machine | `runtime/task/state.rs` | 657 ln | medium | **high** |
| 7 | LIFO slot | `worker.rs:120–126, 265` | ~40 ln | trivial | none (heuristic) |
| 8 | coop budget | `runtime/coop.rs` | small | low | low, but the *policy* needs a stated property |
| 9 | current-thread flavour | `current_thread/mod.rs` | 925 ln | low | medium — a good warm-up target |
| — | drivers (I/O, time) | `runtime/io`, `runtime/time` | ~1 500 ln | **skip** — Lean has libuv | none |

**Read order for anyone implementing:** `multi_thread/mod.rs` → `worker.rs` → `queue.rs` →
`inject.rs` → `park.rs` → `idle.rs`. Then the 2019 blog for *why*, with the caveat that its inject
queue description is stale.
