# Evidence

Every load-bearing claim in this plan is traceable to one of three kinds of source:

| Tag | Meaning |
|---|---|
| **[M]** | **M**easured first-hand on this machine, by a program in this repo. Reproducible: `lake exe spike`. |
| **[S]** | **S**ource read first-hand — a file in an installed toolchain, or a paper/artifact read by a research subagent with a URL. The anchor is given. |
| **[R]** | **R**eported by a research subagent from a named source, not independently re-read. Treat as a lead, not a fact. |

______________________________________________________________________

## 1. Environment

```
$ lean --version                 # elan's toolchain: the release tarball for this version
Lean (version 4.35.0-rc3, x86_64-unknown-linux-gnu, commit 470d5ce1400764999581fd26d5d72b00d990b0f4, Release)
$ nix develop -c lean --version  # the nix dev shell
Lean (version 4.35.0-rc3, Release)
$ nproc
8
```

Two ways to get that toolchain, and both resolve the same release. The nixpkgs build sets
`USE_GITHASH=false`, so its version string carries neither the commit nor the target triple; the part
that matters is the version, `4.35.0-rc3`, which both report.

- **Nix** (the default here): `flake.nix` derives `lean4` from nixpkgs' own `lean4` derivation with
  the source and version moved to the `v4.35.0-rc3` tag, and tracks `nixos-unstable` with no revision
  written into the flake. Commands run as `nix develop -c lake …`. The derivation is built from
  source against the store's `gmp`, `libuv` and `openssl` **[S]** (nixpkgs
  `pkgs/by-name/le/lean4/package.nix`), so the toolchain comes from the shell's closure rather than
  from a self-contained tarball.
- **elan**: `lean-toolchain` names `leanprover/lean4:v4.35.0-rc3`; toolchains v4.25.2 … v4.35.0-rc3 are
  installed locally **[S]**.

All measurements below were produced through the **nix dev shell** and reproduce the same figures
through elan; the two runs agree to the millisecond on the headline numbers.

Rationale for the pin: `Std.WP` exists **only** in the 4.35 line and not in v4.34.1 or v4.31.0 **[S]**
(`ls <toolchain>/src/lean/Std/` on each; `Std/WP/` present only in 4.35). `Std.Async` is present from
v4.31.0 onward **[S]**. The 4.35 line is still pre-release — `v4.35.0-rc4` is the newest upstream tag
**[S]** — so the pin names an RC deliberately, and bumping it means re-checking that `Std.WP` and
`Std.Async` still have the shape this plan assumes.

______________________________________________________________________

## 2. Measured: what Lean 4.35's scheduler actually does

Harness: `Spike.lean`, built and run as `lake exe spike`. It spawns tasks, samples
`IO.getTID`, and times blocking vs. non-blocking sleeps under contention.
Output, verbatim (single run, idle machine):

```
hardware concurrency: 8
64 tasks, default prio   : 7 distinct threads
64 tasks, dedicated prio : 64 distinct threads
64x IO.sleep 100ms, default   : parallel 801ms / serial 6406ms
64x IO.sleep 100ms, dedicated : parallel 103ms
Async.async 2x IO.sleep 200ms: 200ms
64x Async.sleep 100ms        : 102ms
Promise handoff: 42
Channel sum 0..99 (bounded 4): ok: 4950
Channel sum 0..99 (unbounded): ok: 4950
```

Readings **[M]**:

1. **The task pool is bounded by the core count and does not scale with offered parallelism.**
   64 tasks at `Task.Priority.default` were observed on **7–8** distinct OS threads across runs
   (8 on an earlier run, 7 on a later one) — i.e. ≤ `hardware concurrency`. This is a fixed pool,
   not a growable one.

1. **`Task.Priority.dedicated` escapes the pool entirely.** 64 tasks at `dedicated` (priority 9)
   used **64 distinct threads** — one thread per task. This is the only "get off the pool" escape
   hatch Lean offers, and it is per-task, not a bounded blocking pool.

1. **Blocking work on the pool causes head-of-line blocking.** 64 tasks each doing
   `IO.sleep 100` took **801 ms** — `ceil(64/8) × 100 ms`, i.e. exactly 8 rounds over 8 workers.
   The blocking sleep *occupies a worker thread*. Serial baseline: 6406 ms for the same 64 sleeps.

1. **The `Async` layer is genuinely non-blocking.** 64 concurrent `Async.sleep 100` (libuv timer)
   completed in **102 ms** — the 64 timers did not consume 64 pool workers; they did not consume
   *any* pool worker while waiting. This is the single most important measured fact in the plan:
   the async path already has a working reactor, and the *blocking* path is the hole.

1. **`await` on the async path runs two `IO.sleep 200` computations concurrently** (200 ms, not
   400 ms), confirming `Async.async`/`await` composes into real parallelism **[M]**.

1. `IO.Promise` handoff and `CloseableChannel` (bounded capacity 4, and unbounded) both work
   correctly across tasks, summing 0..99 to 4950 **[M]**.

### Pool width is a dial, and the two sleep paths diverge

Run with `LEAN_NUM_THREADS` set, through the nix dev shell **[M]**:

| `LEAN_NUM_THREADS` | distinct threads seen | 64 × `IO.sleep 100` | 64 × `Async.sleep 100` | `Async.async` 2 × `IO.sleep 200` |
|---|---|---|---|---|
| 1 | 1 | 6406 ms | 102 ms | 401 ms |
| 2 | 1 | 3203 ms | 102 ms | 200 ms |
| 4 | 4 | 1602 ms | 101 ms | 201 ms |
| 8 (default) | 7–8 | 801 ms | 102 ms | 200 ms |

`IO.sleep` scales exactly as `ceil(64/N) × 100 ms`, confirming one blocked worker per sleeping task,
and confirming that `LEAN_NUM_THREADS` sizes the pool as the runtime source says it does
(`docs/lean-scheduler.md` §4). `Async.sleep` is **flat at ~102 ms even at `LEAN_NUM_THREADS=1`**,
because the libuv loop thread services timers and consumes no pool worker (§6).

⚠️ **Methodological correction.** At `LEAN_NUM_THREADS=2` the thread-identity probe saw only **one**
distinct thread while the timing probe proves two workers were active. `tidsOf` spawns 64 trivial
tasks, which the pool services from whichever worker is idle — it measures concurrency *exercised by
short tasks*, not pool width. **For pool width, the timing probe is the reliable instrument and the
TID probe is a lower bound.** Earlier readings of "7–8 distinct threads" in §2 should be read the same
way.

### Consequence for the roadmap

The head-of-line blocking in (3) is precisely the problem Tokio solves with `spawn_blocking` and a
separate blocking pool, and (1) is precisely the problem Tokio's work-stealing scheduler solves by
letting idle workers steal rather than sit parked. Both are real, both are measured, and neither is
hypothetical. The library's first two milestones are aimed at exactly these two facts.

______________________________________________________________________

## 3. Read first-hand: the shape of Lean's concurrency stack

All anchors are under `<toolchain>/src/lean/` for v4.35.0-rc3 **[S]**.

| Layer | Module | Bound to |
|---|---|---|
| `Task`, `Task.spawn`, `Task.map` | `Init/Core.lean` (~:656–775) | `@[extern "lean_task_spawn" / "lean_task_map" / "lean_task_bind"]` |
| `IO.Promise` | `Init/System/Promise.lean` | `lean_io_promise_new`, `lean_io_promise_resolve`, `lean_io_promise_result_opt`, `lean_option_get_or_block` |
| blocking waits, cancellation | `Init/System/IO.lean` | `lean_io_wait`, `lean_io_wait_any`, `lean_io_cancel`, `lean_io_check_canceled`, `lean_io_get_task_state` |
| async monads | `Std/Async/Basic.lean` (998 lines) | Lean-level, built on `Task` + `IO.Promise` |
| event multiplexing | `Std/Async/Select.lean` | `Selector`/`Selectable`/`Waiter`, Lean-level |
| I/O, timers, DNS, signals, processes | `Std/Internal/UV/*.lean` | libuv (`lean_uv_*`) |
| mutexes, condvars | `Std/Sync/{Mutex,RecursiveMutex,SharedMutex}.lean` | `lean_io_base{mutex,recmutex,sharedmutex}_*`, `lean_io_condvar_*` |
| channels, semaphores, broadcast | `Std/Sync/{Channel,Semaphore,Broadcast,Barrier,Notify,StreamMap}.lean` | Lean-level on top of `AtomicT` + `IO.Promise` |
| cancellation | `Std/Sync/{CancellationToken,CancellationContext}.lean` | Lean-level |
| program logic | `Std/WP/**` (≈4 775 lines) | Lean-level, **sequential only** |

Two structural facts that matter for the TCB story **[S]**:

- `AtomicT := StateRefT' IO.RealWorld` (`Std/Sync/Basic.lean`, 22 lines total, `abbrev`). It is a
  *state monad*, not an atomic primitive. The atomicity that `Std.Sync` primitives rely on comes
  from running an `AtomicT` action inside a `Mutex` whose implementation is the C++
  `lean_io_basemutex_*`. **Every `Std.Sync` primitive's correctness therefore rests on the C++
  mutex/condvar, which is outside Lean's kernel.**
- The task manager and thread pool are C++, not Lean. The Lean reference states the pool size comes
  from `LEAN_NUM_THREADS` or the logical processor count, and that the size "is not a hard limit"
  **[S]** (`lean-lang.org/doc/reference/latest/IO/Tasks-and-Threads`).

______________________________________________________________________

## 4. Reported: supporting facts

- Lean's runtime uses **C++11 `seq_cst` atomics** for refcounts and task fields
  (`src/include/lean/lean.h`; `src/runtime/thread.cpp` uses pthreads) **[R]**.
- The runtime contains **no ThreadSanitizer instrumentation** and exposes **no deterministic
  scheduler hook** (code search for `fsanitize=thread` / `__tsan` in `leanprover/lean4`: 0 results)
  **[R]**. Determinism must come from `LEAN_NUM_THREADS` / `-j<N>`, repeated runs, and
  `IO.setRandSeed` (which does make `Std.Async.Select`'s fairness shuffle reproducible — it shuffles
  selectables using `IO.stdGenRef`) **[S]**.
- `Std.Async.Async.race` **does not cancel the loser** **[S]** (documented in `Std/Async/Basic.lean`;
  `ContextAsync.race` is the structured variant that does).
- Lean's largest in-tree concurrency design is `Lean.Language`'s snapshot engine, hand-rolled on
  `IO.Promise` + `Task` and *not* using `Std.Async` **[R]**.
- The C++ runtime lives at `src/runtime/task_manager.cpp`, `object.cpp`, `thread.cpp` upstream
  **[R]**; the binary toolchain distribution does *not* ship those `.cpp` files, only `.a`/`.so`
  **[S]** — so runtime source must be read upstream, not locally.

______________________________________________________________________

## 5. Measured: the `Task`-as-waker bridge

Harness: `WakerSpike.lean`, run through the nix dev shell. Reproduces the O3 spike behind D10 in
[`decisions.md`](decisions.md).

```
$ for i in 1 2 3; do ./wakerspike; done
  main     tid=3185063
  carrier  tid=3185064  started
  carrier  tid=3185064  consumed "event:ok: 7" (waker tid=3185065)
  carrier  joined
  pool tids sampled: [3185065, 3185066]
  waker tid=3185065   carrier tid=3185064
  CHECK distinct threads (the seam) : true
  CHECK carrier not a pool worker  : true
  CHECK waker was a pool worker    : true
        (runs 2 and 3 identical in shape)
```

Readings **[M]**:

1. **An external `Task` completion can be routed into our own data structure.** `BaseIO.bindTask`
   attaches a continuation whose body pushes into a mutex-guarded inbox; the completion runs on the
   pool, the *work* runs on our carrier. This is the mechanism D3 depends on.
1. **The waker and the carrier are different threads**, reproducibly, across runs.
1. **`IO.println` is unavailable in a `bindTask` continuation** — it is `IO Unit`, the continuation is
   `BaseIO (Task β)`. Instrumentation built on this seam must carry its observations as data.
1. **`IO.asTask` wraps its result in `Except IO.Error`**, so a bound continuation receives
   `Except IO.Error α` (visible as `event:ok: 7` above) rather than a bare `α`.

⚠️ **Limits of this instrument.** The "carrier not a pool worker" and "waker was a pool worker" checks
compare against a *sampled* set of pool thread ids (32 trivial tasks), which is a lower bound on the
pool's real membership, not its actual membership. Only the first check — the two tids are distinct —
is conclusive. The claim that a `dedicated`-priority task gets its own OS thread rests on the runtime
source (`object.cpp:792` → `spawn_dedicated_worker`), not on this harness.

______________________________________________________________________

## 6. Measured: the runtime controls

Harness: `LeanIn/Test/Control.lean`, run as `nix develop -c lake exe controls`. One control per bridge
axiom, so that `LeanIn/Theory/Bridge.lean`'s claims are not assertions.

```
$ ./controls
controls for the bridge axioms
  A3 (release without ownership) and A6 (thread creation) are not tested — see the header.

  A7  10000 reads, 0 regressions, 10000 advances : monotone = true
  A2  tryLock while held → false : true
  A2  tryLock while free → true  : true
  A2  the evidence for `true` is that it *returned* while the lock was held; the 209344 ns
      it took is mostly the thread round-trip and proves nothing on its own
  A5  after a lost notify + 200ms, waiter is : running
      (`running` here means started-and-not-finished, i.e. still parked — a parked task
       reports as `running` because its closure has been taken; see `object.cpp:1080`)
  A5  after notifyAll + 200ms, waiter is        : finished
  A4  after a wake with the predicate false : running  (re-parked = correct)
  A4  after the predicate becomes true      : finished
  A1  4 threads x 500000 increments = 2000000 expected
  A1  unguarded → 1828304  (171696 lost)
  A1  guarded   → 2000000  exact = true  (affirmative control)
```

Readings **[M]**:

1. **A1 — mutual exclusion is load-bearing.** Without a lock, 4 threads × 500 000 increments lost
   between 171 696 and 536 621 updates across runs (a quarter of them); with a `Std.Mutex` the total is
   exactly 2 000 000. The guarded half is the **affirmative control**: it shows the counter and the
   threads are real, so the loss is attributable to the missing lock.
1. **A2 — `tryLock` observes a held lock and returns.** The `tryLock` is issued from a *second* thread,
   because `std::mutex::try_lock` on a mutex already held by the calling thread is undefined behaviour
   — the naive control would have been the defect it is meant to detect.
1. **A5 — a notification with no waiter is lost.** `notifyOne` before anyone parks leaves the waiter
   parked indefinitely (after 200 ms it is still not `finished`); `notifyAll` then resumes it. This is
   the runtime counterpart of the proved `notifyOne_no_waiters`.
1. **A4 — a `waitUntil` shape tolerates a wakeup it did not ask for.** Woken with the predicate false,
   the waiter re-parks; when the predicate becomes true, it finishes. This is a *tolerance* test, not an
   observation of a spurious wakeup.
1. **A7 — the clock never went backwards** across 10 000 reads, and advanced on every one.

⚠️ **Limits of these controls.** A1 is a **race**: loss is expected but not guaranteed on any given
run, and the count is printed rather than asserted. **A3 and A4 cannot be tested as claimed** — A3
because violating it is undefined behaviour, so the test *is* the defect; A4 because the implementation
is permitted to wake spuriously, not obliged to, so a spurious wakeup cannot be forced. Both are
discharged by reading `mutex.cpp` against the standard, and A3 additionally by the model having no
transition for it (`unlock_without_ownership_has_no_transition`). **A6** is absent from v1.

______________________________________________________________________

## 7. Reported: what is *not* proven anywhere

Checked deliberately, because a negative here is a research contribution:

- **No formal semantics of Lean's `IO`/`Task`/`Promise`/`ST.Ref` concurrency exists** — not
  machine-checked, not pen-and-paper, not a manual-level operational semantics. What exists is a
  typing discipline for effect ordering (`IO.RealWorld` is `opaque`). The `@[extern]` bodies for the
  concurrency primitives are **placeholder stubs, not models**: `Task.spawn (fn) := ⟨fn ()⟩` runs the
  computation *eagerly on the current thread*, and `Ref.get r := inhabitedFromRef r` returns an
  **arbitrary inhabitant**. This is the decisive contrast with `Array`/`String`/`ByteArray`, whose
  externs carry *correct* pure bodies, and it is why the established "prove the pure body, trust the
  extern" discipline does not currently extend to concurrency.
  `Std.WP` soundness covers `Id`/`Option`/`Except`/`EStateM`/`StateT`/`ReaderT`/`OptionT`/`ExceptT`
  and has **no `IO`, `BaseIO`, `EIO`, `Task`, `Promise`, `ST` or `ST.Ref` instance**; `BaseIO`'s
  `MonadAttach` is the *trivial* one, so it is inert for reasoning. `iris-lean` models HeapLang, not
  Lean's `IO`. `lean4lean` covers only the kernel. **[S]**
- **No machine-checked work-stealing deque, scheduler, or scheduling bound in Lean** (Mathlib docs,
  web, GitHub searched) **[R]**.
- **No formalized work/span scheduling theory anywhere in a proof assistant** — no Graham bound, no
  Brent theorem, no DAG makespan, no list scheduling. They are cited as folklore in the work-stealing
  literature, not re-proved **[R]**.
- **No machine-checked proof of a full async executor** (user-visible properties: no lost wakeups,
  cancellation, completion, fair scheduling) **[R]**. The nearest artifacts are Rocq.
- **`TASOR` does not exist.** The framework previously believed to exist under that name
  (Mével/Jourdan/Pottier, "A Theory of Provably-Correct Work Stealing") could not be found in GitHub
  repository search, the HAL API, François Pottier's own publication list, or Glen Mével's homepage.
  The real predecessors/candidates are **Parabs**, **Parcas**, **Cosmo**, and **BWoS** — see the
  reading list **[R]**.
