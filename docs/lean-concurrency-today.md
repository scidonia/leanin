# Lean 4 concurrency as it stands

Verdict, in one paragraph: \*\*Lean 4.35 already ships a Tokio-shaped *surface* — tasks, promises,
`async`/`await`, cancellation contexts, channels, semaphores, a `select` protocol, timers, TCP/UDP,
DNS and an HTTP server, all on a libuv reactor — but underneath that surface is a single *global
priority thread pool with no work-stealing, no per-worker run queues, and no blocking pool*, and
**none of it is verified**. So `leanin` is not "build a runtime from nothing". It is "(a) replace the
scheduler under an existing, working async layer, and (b) prove things about it that nothing in the
Lean ecosystem currently proves."

______________________________________________________________________

## 1. Layer map

Anchors are `<toolchain>/src/lean/` in v4.35.0-rc3 unless stated **[S]**.

| Layer | Module(s) | Implemented by | Status |
|---|---|---|---|
| Task, priority, spawn/map/bind | `Init/Core.lean` `:656–775` | C++ runtime, `@[extern "lean_task_spawn"]` etc. | stable |
| Promise | `Init/System/Promise.lean` | C++ (`lean_io_promise_*`) | stable |
| blocking waits, cancel, state | `Init/System/IO.lean` | C++ (`lean_io_wait`, `lean_io_cancel`, …) | stable |
| `Mutex`, `Condvar` | `Std/Sync/Mutex.lean` | C++ (`lean_io_basemutex_*`, `lean_io_condvar_*`) | stable |
| `RecursiveMutex`, `SharedMutex` (RwLock) | `Std/Sync/*` | C++ | stable |
| `Barrier`, `Semaphore`, `Notify`, `Broadcast`, `Channel`, `StreamMap` | `Std/Sync/*` | Lean, over `AtomicT` + `IO.Promise` | stable |
| `CancellationToken`, `CancellationContext` | `Std/Sync/*` | Lean | stable |
| `BaseAsync`/`EAsync`/`Async`, `async`/`await`, `race`, `concurrently`, `background` | `Std/Async/Basic.lean` (998 ln) | Lean, over `Task` + `Promise` | stable |
| `Selector`/`Selectable`/`Waiter` (event multiplexing, randomised fairness) | `Std/Async/Select.lean` | Lean | stable |
| structured cancellation (`ContextAsync`, `fork`, `disown`) | `Std/Async/ContextAsync.lean` | Lean | stable |
| `Async.sleep`, timers | `Std/Async/Timer.lean` | libuv | stable |
| TCP/UDP/DNS/signals/processes | `Std/Async/{TCP,UDP,DNS,Signal,Process,System}.lean` | libuv via `Std/Internal/UV/*` | stable |
| `AsyncRead`/`AsyncWrite`/`AsyncStream` | `Std/Async/IO.lean` | Lean | stable |
| HTTP server | `Std/Http/**` | Lean + libuv | stable |
| program logic (sequential) | `Std/WP/**` (≈4 775 ln) | Lean | **4.35 only**, sequential |
| snapshot engine | `Lean/Language/**` | `IO.Promise` + `Task`, hand-rolled | stable |

Version history **[S]**: `Std.Internal.Async` existed from v4.27.0; promoted to the public
`Std.Async` namespace in v4.31.0 (PR `leanprover/lean4#11454`). `Std.Sync` predates it. `Std.WP`
appears only in v4.35.0-rc3.

Two notes on the trusted boundary **[S]**:

- `AtomicT` is `abbrev AtomicT := StateRefT' IO.RealWorld` (`Std/Sync/Basic.lean`, the whole file is
  22 lines). It is a **state monad, not an atomic primitive**. Atomicity is inherited from running
  the action under a C++ mutex. Every `Std.Sync` primitive built this way is correct only because the
  C++ mutex is.
- `Std.Async` is a *thin monadic shell over `Task`*. There is no separate executor object, no
  `Runtime::new`, and no way to substitute a scheduler. `Task.spawn` is the scheduler.

______________________________________________________________________

## 2. What the scheduler actually is

`Task.Priority := Nat` (`Init/Core.lean:656`) **[S]**:

```
Priority.default   = 0   -- lowest
Priority.max       = 8   -- highest pool priority (see LEAN_MAX_PRIO)
Priority.dedicated = 9   -- any priority > max runs on a dedicated OS thread
```

- One global priority-ordered pool. Pool size = `LEAN_NUM_THREADS` or the core count **[S]**
  (`object.cpp:1106`), and it "is not a hard limit" because `Task.get` from a pooled task raises the
  cap temporarily (`object.cpp:1020–1042`).
- **No per-worker run queue and no stealing** — but there *are* queues: **nine shared `std::deque`s,
  one per priority 0–8, all behind a single mutex**, drained highest-priority-first and FIFO within a
  priority (`object.cpp:753–804`). See [`docs/lean-scheduler.md`](lean-scheduler.md) for the full
  reading — this section is a summary of it.
- The escape from the pool is a per-task dedicated thread (priority > 8), which gives you *n* threads
  for *n* blocking tasks rather than a bounded blocking pool.

Measured on this machine (8 cores) **[M]** — see `docs/evidence.md` for the harness:

| Probe | Result | Reading |
|---|---|---|
| 64 tasks @ default priority | 7–8 distinct threads | pool is capped at core count |
| 64 tasks @ `dedicated` | 64 distinct threads | one thread per task; not a pool |
| 64 × `IO.sleep 100` | **801 ms** | blocking work occupies a worker: `ceil(64/8)×100` |
| 64 × `Async.sleep 100` | **102 ms** | libuv timers do not consume workers |
| `Async.async` × 2 × `IO.sleep 200` | 200 ms | `async`/`await` composes into real parallelism |

The two rows in bold are the design drivers. **Head-of-line blocking of the pool by blocking work**
is exactly what Tokio's `spawn_blocking` pool exists to prevent. **A capped pool with no stealing**
is exactly what Tokio's work-stealing scheduler exists to fix.

______________________________________________________________________

## 3. How to use Lean concurrency today

Idioms, all exercised in `Spike.lean` **[M]**:

```lean
-- Spawn and join. `IO.asTask` takes an `IO` action; result is `Task (Except IO.Error α)`.
let t ← IO.asTask (IO.sleep 100) Task.Priority.default
let r ← IO.wait t                       -- r : Except IO.Error Unit

-- Promise: hand a value across tasks.
let p ← IO.Promise.new (α := Nat)
let c ← IO.asTask do let r ← IO.wait p.result?; return r.getD 0
p.resolve 42

-- async/await: `await` never blocks an OS thread; the continuation is scheduled back.
Std.Async.Async.block do
  let a ← async (IO.sleep 200)
  let b ← async (IO.sleep 200)
  await a; await b

-- Channel, bounded and unbounded, one API.
let ch ← CloseableChannel.new (α := Nat) (capacity := some 4)
let t ← ch.send 7      -- t : Task (Except CloseableChannel.Error Unit)
let r ← ch.recv        -- r : Task (Option Nat); `none` after close
```

Ergonomics findings worth recording because they cost time:

- **`open Std` is not enough for `Async.block`.** The runner's full name is
  `Std.Async.Async.block` (the namespace `Std.Async.Async` shadows the `Async` abbreviation), and
  `monad`/`await` need `open Std.Async` for the `MonadAsync`/`MonadAwait` class methods to resolve.
  The doc-comment examples read as though `Async.block` suffices.
- **A `def main` inside a `namespace` silently links the toolchain's default `_lean_main`**, which
  pulls `libLeanExport.a` into the link and fails with ~250 unresolved `l_Lean_*` symbols. `main`
  must be at root scope. This is a real trap for anyone building an executable library.
- `race` **does not cancel the loser** **[S]**; `ContextAsync.race` does.

______________________________________________________________________

## 4. Gap to a Tokio-shaped library

| Tokio component | Lean today | Verdict |
|---|---|---|
| `Task`, `spawn`, `JoinHandle` | `Task`, `IO.asTask`, `IO.wait` | **reuse** |
| `Waker`/`RawWaker` plumbing | `IO.Promise` + task continuations | **reuse** |
| future poll contract | `MonadAwait`/`MonadAsync`, `Async` monads | **reuse** (different shape, same power) |
| `select!` | `Std.Async.Select` (`Selector`/`Selectable`, randomised fairness) | **reuse**, ergonomics thin |
| timers | `Std/Async/Timer.lean` via libuv | **reuse** |
| I/O reactor | libuv via `Std.Internal.UV` (epoll under the hood) | **reuse** |
| sync primitives | `Std.Sync` complete set | **reuse** |
| `CancellationToken` | `CancellationContext`/`Token` + `ContextAsync` | **reuse** |
| HTTP server | `Std.Http.Server` | **reuse** |
| **work-stealing multi-thread scheduler** | none — global priority pool | **build** |
| **per-worker run queue + LIFO slot + inject queue** | none | **build** |
| **`spawn_blocking` / bounded blocking pool** | none (per-task dedicated thread only) | **build** |
| `LocalSet` / non-`Send` tasks | none | **build** |
| `current_thread` runtime flavour + `block_on` | none (no runtime object at all) | **build** |
| runtime handle, `shutdown`, graceful stop | none | **build** |
| `#[tokio::test]` paused-time / deterministic runtime | none; no scheduler hook exists **[R]** | **build** |
| task-local storage | none | **build** (easy) |
| `JoinSet`-style dynamic task sets | none | **build** (easy) |
| io_uring | libuv = epoll | **out of scope** |
| **proofs** | none, anywhere | **build (the actual research)** |

### How much work, honestly

- **Reuse is larger than expected.** The reactor, timer wheel, socket layer, cancellation algebra,
  channels and semaphores are done and working. A Tokio-style *surface* is mostly a `select!`-shaped
  ergonomics layer over what already exists.
- **The scheduler is the real build.** Tokio's multi-thread scheduler is a per-worker local deque
  (Chase–Lev-like, with its own provenance), a LIFO slot, a global inject queue, a steal protocol
  with retry/lost states, a park/unpark protocol, and a coop budget. That is the piece Lean does not
  have, and it is the piece this project is named after.
- **Two hard external constraints** shape everything: (i) Lean gives no hook to *replace* `Task`'s
  scheduler, so a `leanin` scheduler must be a scheduler *over* `Task` (worker threads that own
  `leanin` queues) or must require a runtime patch; (ii) there is **no `Task`-level waker**, so
  waking a parked `leanin` worker must be built on `IO.Promise`/`Mutex`+`Condvar`/`Task.spawn`.
  Deciding (i) and (ii) is milestone 0 of the plan.
- **The proof obligation is unclaimed ground.** No machine-checked work-stealing deque, scheduler,
  or scheduling bound exists in Lean, and no formal semantics of Lean's `IO`/`Task` exists at all
  **[R]** (see `docs/proof-strategy.md` for what that forces).

______________________________________________________________________

## 5. What you can test with today

- `LEAN_NUM_THREADS=<n>` sets the pool size; `lean`/`lake -j<n>` sets `ShellOptions.numThreads`
  **[R]**. Setting it to 1 gives a quasi-single-threaded run.
- **No ThreadSanitizer instrumentation** exists in the Lean runtime, and **no deterministic
  scheduler hook** **[R]** (code search for `fsanitize=thread`/`__tsan`: 0 results).
- `IO.setRandSeed` makes `Std.Async.Select`'s fairness shuffle reproducible **[S]**.
- So race detection today = repeated runs × varied `LEAN_NUM_THREADS` × varied priorities. There is
  no `Loom`/`shuttle` equivalent and no `miri` equivalent. **A deterministic scheduler is a deliverable
  of this project, not an assumption** — and it is also the thing that makes the proofs testable.
