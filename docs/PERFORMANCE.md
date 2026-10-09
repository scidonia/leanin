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
- `--runtime-bench` and `--runtime-async` report the **best of 5** runs, `--runtime-ops` and `--runtime-unit`
  the best of 2.
- **Run-to-run drift is ±30%, so no single pair of numbers attributes anything.** In one session the *same*
  10 000-task workload read 7 713 µs in one diagnostic and 10 795 µs in another; the stock pool's own row moved
  26 579 ↔ 28 549 µs across days. A comparison between two revisions has to interleave them and take minima —
  which is how the 1.5× from `Executor`'s ownership fix was measured, and why `--runtime-async` exists.
- Both pool sizes are reported for `Std.Async`: its default thread count (8 here) *and* `LEAN_NUM_THREADS=1`,
  the equal-thread comparison for our single carrier.

## 2. The server-shaped workload: 10 000 tasks, one mutex each, spawned then joined

`nix develop -c lake exe controls --runtime-async`

| configuration | per 10 000 units | against ours |
|---|---|---|
| **leanin**, 1 worker | 10 795 µs | — |
| **leanin**, 2 / 4 / 8 workers | 8 019 / 7 988 / 8 106 µs | 1.35× better, then flat |
| **leanin**, same shape with no body | 8 269 / 8 436 µs | the body is free; this is all machinery |
| **leanin**, same workload from `--runtime-bench` | 7 713 µs | the drift above, same shape |
| stock `Task` pool, default priority | 26 579 µs | **3.4× slower** |
| `Std.Async`, default threads (8) | 131 291 / 145 274 µs | **13–17× slower** |
| `Std.Async`, `LEAN_NUM_THREADS=1` | 24 910 µs | **2.2× slower** |
| `Std.Async`, `LEAN_NUM_THREADS=8` | 125 699 µs | **10× slower** |

Two things worth taking from the table. `Std.Async` gets *worse* the more threads it is given on this shape —
25 ms at one thread, 126 ms at eight — because its tasks are `Task`s on the stock pool, whose nine priority
deques all sit behind one mutex; concurrency buys contention rather than throughput. And our own row is flat
from two workers on, because the client awaits its handles in order, so this workload is serial by
construction: it measures the critical path, not throughput, and more carriers cannot shorten a serial path.

## 3. Where we are ahead

| shape | ours | the other one | source |
|---|---|---|---|
| 10 000 tasks spawn+join | 7 713 µs | `Std.Async` 131 291 µs, stock pool 26 579 µs | `--runtime-bench` |
| the same at equal thread count (1) | ~11 000 µs | `Std.Async` 24 910 µs | `--runtime-async`, `LEAN_NUM_THREADS=1` |
| enqueue, one call | 464 ns | stock `Task` spawn+join 5 499 ns | `--runtime-ops` |
| spawn and await, one round trip | 1 042 ns | stock `Task` spawn+join 5 499 ns | `--runtime-ops` |
| tail: last of 10 000 tasks started | 14 038 µs after the first | stock pool 46 013 µs | `--runtime-tail` |
| shared counter, 10 000 increments | 14 014 µs (a plain `IO.Ref`, correct for one carrier) | stock pool with the mutex its 8 threads require: 49 741 µs | `--runtime-shared` |
| four 50 ms timers on one carrier, via libuv | 51 ms | serial would be 200 ms | `--runtime-sleep` |
| critical section, notification | 27 ns / 1 ns | — | `--runtime-ops` |

The last three are the interesting ones. The tail row says an idle worker does not have to be a slow one: a
task pushed while others run is picked up promptly. The shared row compares each design under the discipline it
actually needs — ours is single-carrier, so a plain reference is correct and wins; the stock pool cannot drop
its lock, and the same diagnostic shows why (`253 115 of 800 000` increments survive without it). And the timer
row is the one that shows the *async* path is genuinely non-blocking while the blocking path is the hole below.

## 4. Where we are worse

Stated first because it is the honest part of this document.

### 4.1 Blocking work stops everything — 4× worse than the stock pool

```
4 x 25ms sleeps      : stock 25134us / leanin 100375us
64 spawned tasks     : 1 distinct threads
```

Four tasks that sleep with `IO.sleep` take **100 ms** on our runtime and 25 ms on the stock pool: one carrier,
so blocking work serialises it. The stock pool is better here for an uncomfortable reason — it has eight
workers to lose. Either way this is the pathology `spawn_blocking` exists for, and it is the motive for W4.
The measurement to move is this row: it should become ~25 ms when blocking leaves the carrier.

### 4.2 One carrier, so no core parallelism at all

`64 spawned tasks : 1 distinct threads`. Every CPU-shaped handler — TLS, JSON, compression — occupies the one
carrier and nothing else runs. This is structural until W8, and it cannot be measured as a comparison yet,
because there is no second carrier to measure.

### 4.3 A burst into an undrained pool grows its overflow

```
unit: transaction plumbing 41ns | + Pool.submit 830ns | + Pool.spawn 2730ns
```

The lock, the state copy and the scheduler record cost **41 ns**. Adding `Pool.submit` costs 830 ns and
`Pool.spawn` 2 730 ns, because the overflow appends the evicted half to `inject`, which is a `List`: a burst
nothing drains grows it, and the append is proportional to its length. In steady state the same work is
**339 ns for a spawn and a take together**, which is the honest per-item figure — the burst figures are what
happens when nothing takes.

### 4.4 The same, seen from one operation

`Executor.submit` at 951 ns against `spawn+take (steady)` at 339 ns for *two* transactions. Same cause as 4.3.
`Executor.spawn` (464 ns) does not show it because it writes the LIFO slot and only occasionally reaches the
ring.

### 4.5 A ring mutation still copies its slots when the array is shared

```
unit: Ring.push unique array 6ns | array shared with a live ring 121ns
```

20× the cost, for a 2 KB copy, whenever the array is referenced twice. `Executor` now releases the cell's hold
before it modifies the pool, which is where that sharing came from, and the take path asks the scheduler before
it reads the pool — but the row stays in the harness because the effect is easy to reintroduce.

### 4.6 This shape does not scale, and is not evidence of scaling

1 worker 10 795 µs, 4 workers 7 988 µs, 8 workers 8 106 µs. A 1.35× gain and then a plateau. That is the
client's in-order `await` loop, not the scheduler, and it means this row cannot be used to argue for or against
multi-carrier work: W8 needs a parallel-shaped workload and a second measurement to go with it.

### 4.7 Measurement itself is a limitation

There is no paused clock and no deterministic driver yet (W13), so anything timeout-shaped can only be tested
against wall-clock time, and there is no ThreadSanitizer in the runtime. Combined with the ±30% drift above,
that means small effects cannot be resolved at all today: the reorder in `Executor`'s take path was worth
2–8%, which is inside the noise of a single run and needed five interleaved pairs to see.

## 5. Rows that are about Lean's pool, not about us

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

## 7. What these numbers are not

- **Not a gate.** They are printed, never asserted: a timing assertion is a flake with a schedule.
- **Not evidence about correctness.** That is SC1–SC6 at the executor boundary, the model's obligations, and
  the controls in `docs/evidence.md`.
- **Not a comparison with Tokio.** None runs here; the Rust reference copy is for the algorithms.
- **Not a claim about a different machine.** Same toolchain, same box, `nice -n 19`.
