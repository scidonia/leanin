# Performance

Measured on this machine, against the two things worth comparing against: **`Std.Async`** — Lean's own async
layer, which is what a Lean service would use today — and the **stock task pool** underneath it (`IO.asTask`),
which is the only scheduler Lean currently has. Tokio is not a comparison here: it is Rust, and the copy under
`Vendor/tokio/` is an algorithm reference, not something that runs in this toolchain.

Every row is a diagnostic in `LeanIn/Test/Control.lean`, reproducible with the command printed beside it. None
of them gates anything: a check that reads elapsed time is a check that fails on a busy machine, which is why
the repository's *checks* are scenarios with controls and these are measurements.

## 1. How to read these

- 8 cores, through the nix dev shell, which runs `lake` under `nice -n 19` — for our rows and for the baselines
  alike, so the handicap is shared.
- 🟢 means **leanin is better**, 🔴 means **leanin is worse**, ⚪ means the row is **not a comparison** — a fact
  about our own runtime, or two numbers that are not like-for-like. Markdown has no colour, so markers carry it
  here, as `⚠️` already does elsewhere in `docs/`; the same figures are coloured where they are reported.
- `--runtime-bench` and `--runtime-async` report the **best of 5** runs, `--runtime-ops` and `--runtime-unit`
  the best of 2.
- **Run-to-run drift is ±30%, so no single pair of numbers attributes anything.** In one session the *same*
  10 000-task workload read 7 713 µs in one diagnostic and 10 795 µs in another; the stock pool's own row moved
  26 579 ↔ 28 549 µs across days. A comparison between two revisions has to interleave them and take minima —
  which is how the 1.5× from `Executor`'s ownership fix was measured, and why `--runtime-async` exists.
- **Every multiplier in the two tables is computed inside the run that printed both of its numbers.** Pairing a
  figure from one run with one from another gives a multiplier that can be off by 1.3×, which is why the same
  workload's advantage over `Std.Async` appears as 17.0× in one pairing and 13.5× in the next. Where a
  comparison crosses runs it is marked as such rather than quietly multiplied.
- Both pool sizes are reported for `Std.Async`: its default thread count (8 here) *and* `LEAN_NUM_THREADS=1`,
  the equal-thread comparison for our single carrier.

## 2. The server-shaped workload: 10 000 tasks, one mutex each, spawned then joined

`nix develop -c lake exe controls --runtime-async`, and the same workload from `--runtime-bench`.

| run | ours | against | ours is |
|---|---|---|---|
| `--runtime-bench` | 7 713 µs | stock `Task` pool, default priority: 26 579 µs | 🟢 **3.4× faster** |
| `--runtime-bench` | 7 713 µs | `Std.Async`, default threads (8): 131 291 µs | 🟢 **17.0× faster** |
| `--runtime-async` | 1 worker: 10 795 µs | `Std.Async`, default threads: 145 274 µs | 🟢 **13.5× faster** |
| `--runtime-async` | 2 / 4 / 8 workers: 8 019 / 7 988 / 8 106 µs | the same `Std.Async` row | 🟢 **18× faster** |
| `--runtime-async`, `LEAN_NUM_THREADS=1` | 1 worker: 11 370 µs | `Std.Async`: 24 910 µs | 🟢 **2.2× faster** |
| `--runtime-async`, `LEAN_NUM_THREADS=8` | 1 worker: 12 040 µs | `Std.Async`: 125 699 µs | 🟢 **10.4× faster** |
| `--runtime-async` | 1 worker vs 2–8 workers | — | ⚪ 1.35× from the second carrier, then flat |
| `--runtime-async` | no body: 8 269 / 8 436 µs | the same rows with the mutex body | ⚪ the body is free; this is all machinery |

The first two rows and the third are the *same* workload measured twice, which is the drift above: 7 713 µs
against 10 795 µs. That is why the headline reads 17.0× in one pairing and 13.5× in the other, and why the
number I would defend is the equal-thread one: **2.2×**.

Two things worth taking from the table. `Std.Async` gets *worse* the more threads it is given on this shape —
24.9 ms at one thread, 125.7 ms at eight — because its tasks are `Task`s on the stock pool, whose nine priority
deques all sit behind one mutex; concurrency buys contention rather than throughput. And our own row is flat
from two workers on, because the client awaits its handles in order, so this workload is serial by
construction: it measures the critical path, not throughput, and more carriers cannot shorten a serial path.

## 3. 🟢 Where we are ahead

Each multiplier is same-run, as in §2.

| shape | ours | the other one | ours is | source |
|---|---|---|---|---|
| 10 000 tasks spawn+join | 7 713 µs | stock `Task` pool 26 579 µs | 🟢 **3.4× faster** | `--runtime-bench` |
| spawn and await, one round trip | 1 042 ns | stock `Task` spawn+join 5 499 ns | 🟢 **5.3× faster** | `--runtime-ops` |
| enqueue, one call | 464 ns | — | ⚪ not like-for-like: the native row is a spawn *and* a join, so set it against the round trip above | `--runtime-ops` |
| tail: last of 10 000 tasks started | 14 038 µs after the first | stock pool 46 013 µs | 🟢 **3.3× better** | `--runtime-tail` |
| shared counter, 10 000 increments | 14 014 µs, a plain `IO.Ref` (correct for one carrier) | stock pool with the mutex its 8 threads require: 49 741 µs | 🟢 **3.5× faster** | `--runtime-shared` |
| four 50 ms timers on one carrier, via libuv | 51 ms | four waits one after another: 200 ms | ⚪ **not a baseline**, for the reason the pair below gives: it shows the timers overlap, which was the point when it was written | `--runtime-sleep` |
| 16 concurrent 50 ms sleeps, one carrier | 51–52 ms | the same 16 sleeps as stock tasks on the pool: 100 ms — two rounds on eight workers, because a blocking sleep occupies the worker it runs on | 🟢 **1.9× better, one thread against eight** | `--runtime-time` |
| those 16 waits issued one after another on one thread | — | 801 ms | ⚪ **not a baseline**: this is what *not* overlapping them costs, which is the reason the row above exists | `--runtime-time` |
| the same 16 sleeps against the shipped *timer* path | 51–52 ms | 64 × 100 ms in 102 ms | ⚪ parity, and a citation rather than a same-run pair (`docs/evidence.md`) | `spike` |
| 16 concurrent echo connections on one carrier | 4.8–11 ms of wall time across runs (≈ 1.5–3.3 k connections/s) | — | ⚪ no baseline yet: the shipped server on this workload is W16 | `--runtime-net` |
| a stop with a connection in flight, draining it | 0.6–1.9 ms to return the loop's value | — | ⚪ not a comparison: the poll interval bounds it, because accept-versus-shutdown is a `select` and we have none yet (W7); an earlier shape whose stop arrived with an empty pool read 95 µs – 1.0 ms | `--runtime-drain` |
| critical section, notification with nobody parked | 27 ns / 1 ns | — | ⚪ no baseline | `--runtime-ops` |

The last three are the interesting ones. The tail row says an idle worker does not have to be a slow one: a task
pushed while others run is picked up promptly. The shared row compares each design under the discipline it
actually needs — ours is single-carrier, so a plain reference is correct and wins; the stock pool cannot drop
its lock, and the same diagnostic shows why (`253 115 of 800 000` increments survive without it). And the timer
row is the one that shows the *async* path is genuinely non-blocking while the blocking path is the hole in §4.

## 4. 🔴 Where we are worse

Stated before anything above it, because it is the honest part of this document. Two rows carry no factor: one
has no baseline to divide by yet, and one is about the instruments rather than the runtime. Each multiplier is
same-run, like every other in this document, and the subsections below explain the mechanism rather than repeat
the arithmetic.

| worse, and where it comes from | ours | baseline | leanin is | source |
|---|---|---|---|---|
| blocking work on a carrier (§4.1) | 100 375 µs | stock pool 25 134 µs | 🔴 **4.0× worse** | `--runtime-bench` |
| no core parallelism at all (§4.2) | 1 distinct thread for 64 tasks | — | ⚪ no baseline yet: structural until W8 | `--runtime-bench` |
| a burst submit into an undrained pool (§4.3) | 830 ns | 41 ns of lock, state copy and enqueue | 🔴 **20× worse** | `--runtime-unit` |
| a burst spawn into an undrained pool (§4.3) | 2 730 ns | the same 41 ns | 🔴 **67× worse** | `--runtime-unit` |
| the submit burst against steady state (§4.4) | 951 ns, one transaction | 339 ns, which is two | 🔴 **2.8× worse** | `--runtime-ops` |
| a ring push whose array is shared (§4.5) | 121 ns | 6 ns, the same push uniquely held | 🔴 **20× worse** | `--runtime-unit` |
| carriers added to a serial client (§4.6) | 1 worker: 10 795 µs | 4 workers: 7 988 µs | 🔴 **1.35×, then flat** | `--runtime-async` |
| what the instruments can resolve (§4.7) | ±30% run-to-run | — | ⚪ no factor: a limit of the measurement, not of the runtime | all of the above |

### 4.1 Blocking work stops everything

```
4 x 25ms sleeps      : stock 25134us / leanin 100375us
64 spawned tasks     : 1 distinct threads
```

Four tasks that sleep with `IO.sleep` take **100 ms** on our runtime and 25 ms on the stock pool, because one
carrier serialises them. The stock pool is better here for an uncomfortable reason — it has eight workers to
lose. Either way this is the pathology `spawn_blocking` exists for, and it is the motive for W4: the row should
become ~25 ms once blocking work can leave the carrier.

### 4.2 One carrier, so no core parallelism

`64 spawned tasks : 1 distinct threads`. Every CPU-shaped handler — TLS, JSON, compression — occupies the one
carrier and nothing else runs. This is structural until W8, and it cannot be measured as a comparison yet,
because there is no second carrier to measure against.

### 4.3 A burst into an undrained pool grows its overflow

```
unit: transaction plumbing 41ns | + Pool.submit 830ns | + Pool.spawn 2730ns
```

The lock, the state copy and the scheduler record cost **41 ns**, and that is the whole of a transaction that
does not touch the pool. `Pool.submit` and `Pool.spawn` add the numbers in the table because the overflow
appends the evicted half to `inject`, which is a `List`: a burst nothing drains grows it, and the append is
proportional to its length. In steady state the same work is **339 ns for a spawn and a take together**, which
is the honest per-item figure — the burst rows are what happens when nothing takes.

### 4.4 The same, seen from one operation

`Executor.submit` sits in the table against `spawn+take (steady)`, and the comparison is deliberately harsh: one
transaction against two. `Executor.spawn` (464 ns) does not show the effect, because it writes the LIFO slot
and only occasionally reaches the ring.

### 4.5 A ring mutation still copies its slots when the array is shared

```
unit: Ring.push unique array 6ns | array shared with a live ring 121ns
```

The copy is 2 KB, and it happens whenever the array is referenced twice. `Executor` now releases the cell's hold
before it modifies the pool, which is where that sharing came from, and the take path asks the scheduler before
it reads the pool — but the row stays in the harness because the effect is easy to reintroduce.

### 4.6 This shape does not scale, and is not evidence of scaling

The 1.35× in the table is the client's in-order `await` loop, not the scheduler, and it means this row cannot be
used to argue for or against multi-carrier work: W8 needs a parallel-shaped workload and a second measurement to
go with it.

### 4.7 Measurement itself is a limitation

Not a claim about the runtime, but about the instruments, and it limits what can be claimed at all. There is no
paused clock and no deterministic driver yet (W13), so anything timeout-shaped can only be tested against
wall-clock time, and there is no ThreadSanitizer in the runtime. Combined with the ±30% drift in §1, small
effects cannot be resolved today: the reorder in `Executor`'s take path was worth 2–8%, which is inside the
noise of a single run and needed five interleaved pairs to see.

## 5. ⚪ Rows that are about Lean's pool, not about us

These appear in the same diagnostics and are the motivation for W4 and W8; they are not comparisons with this
runtime, and they should not be read as such:

```
queue   : 8 workers blocked 300ms; 8 further tasks finished at 300229us
dedicat : 10000 dedicated tasks, one thread each, ran in 476336us
```

`queue` is the stock pool's starvation shape — with all eight workers blocked, ready work does not run at all.
`dedicat` is the only escape Lean offers from the pool: `Task.Priority.dedicated` gives a task its own OS
thread, which is one thread per task rather than a bounded blocking pool.

## 6. Reproduce

| command | what it measures |
|---|---|
| `nix develop -c lake exe controls --runtime-bench` | the two server shapes: 10 000 tasks spawn+join (native, leanin, `Std.Async`) and 4 × 25 ms blocking sleeps; plus the thread count our tasks ran on |
| `nix develop -c lake exe controls --runtime-async` | that workload swept over worker counts, with a no-body control, and the `Std.Async` row; also the one to run under `LEAN_NUM_THREADS=1` and `8` |
| `nix develop -c lake exe controls --runtime-ops` | per-operation costs: enqueue, take, a spawn+await round trip, a critical section, a notification, a reference pair |
| `nix develop -c lake exe controls --runtime-unit` | one transaction decomposed: plumbing, pool operations, and the ring's array sharing |
| `nix develop -c lake exe controls --runtime-tail` | how late the last of 10 000 tasks starts, and the stock pool's starvation and dedicated-thread shapes |
| `nix develop -c lake exe controls --runtime-shared` | the same counter under each design's required discipline, and what the stock pool loses without its lock |
| `nix develop -c lake exe controls --runtime-sleep` | four 50 ms libuv timers on one carrier — 51 ms, against 200 ms for a serial sleep path |
| `nix develop -c lake exe controls --runtime-net` | 16 concurrent echo connections on one carrier: the connection count, the server's thread count, whether the client shares it, the byte-identical replies, and the pool alongside |
| `nix develop -c lake exe controls --runtime-time` | 16 × 50 ms sleeps and their event order, two timeout outcomes, the task layer's first-writer law, and the blocking path for the same sleeps |
| `nix develop -c lake exe controls --runtime-drain` | a stop with a connection in flight: whether the connection completes after the stop, whether the pool is empty and whether a leaf registration is outstanding when the run returns, and how long the drain takes |

## 7. What these numbers are not

- **Not a gate.** They are printed, never asserted: a timing assertion is a flake with a schedule.
- **Not evidence about correctness.** That is SC1–SC6 at the executor boundary, the model's obligations, and
  the controls in `docs/evidence.md`.
- **Not a comparison with Tokio.** None runs here; the Rust reference copy is for the algorithms.
- **Not a claim about a different machine.** Same toolchain, same box, `nice -n 19`.
