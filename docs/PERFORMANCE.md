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

Re-measured after the cancellation milestone, which added a token to the task handle and a read to every step:
`--runtime-bench` read **10 158 / 10 819 / 11 407 / 11 728 µs** across runs, and `--runtime-async` **12 313 µs at one
worker** (12 337 / 12 909 / 12 999 at two, four and eight), against 25 655–26 624 µs for the stock pool and
96 409–147 154 µs for `Std.Async` in those same runs.

**This row reads above its recorded 7 713 µs**, by +31.7% at the lowest of those readings and +52.1% at the
highest — all four outside this document's stated ±30% band, and the two highest also above the 10.2–11.3 ms range
the workplan quotes for it. The two revisions were not interleaved the way §1 requires of a comparison, so the
movement is **not attributed**: this is neither evidence that the milestone moved the row nor evidence that it did
not. What the same-run pairs do establish is that our row stayed ahead of the stock pool and `Std.Async` measured
beside it, and that a gap of this size for *this* workload is within what §1's own example shows between two
diagnostics (7 713 µs against 10 795 µs). Re-measuring with the revisions interleaved is what would settle it.

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
| bounded accept path (`Runtime.serveBounded`): one 5-connection run, bound 2 | 101 630–102 766 µs for the whole run; 20 326–20 553 µs per connection; 48–49 connections/s | — | ⚪ no baseline: the loop is new, and the run's wall time is dominated by the staged 100 ms deadline (id 1's `Runtime.never`), not by admission — the row is what the command reproduces, not an accept-throughput figure | `--runtime-service` |
| a stop with a connection in flight, draining it | 0.6–1.9 ms to return the loop's value | — | ⚪ not a comparison: the poll interval bounds it, because accept-versus-shutdown is a `select` and we have none yet (W7); an earlier shape whose stop arrived with an empty pool read 95 µs – 1.0 ms | `--runtime-drain` |
| a cancellation, decomposed | spawn and await 1.40–1.56 µs without one; spawn and cancel 1.16–1.21 µs; the parts measured alone over one computation and one cell: token set 0.11–0.33 µs, `resolveFirst` 0.14–0.58 µs, **retire 7.9–8.7 µs** (200 iterations each) | — | ⚪ no baseline: the operation did not exist before this milestone. The two whole-operation loops differ in shape as well as in the cancellation they do or do not make, so the parts are the decomposition and the retire is its finding — a linear scan of the registry, measured over the 201 entries the parkers leave, while the cancel loop's own retire scans a registry its own cycles keep empty | `--runtime-cancel` |
| the registration registry, with 200 awaits in flight on a leaf | 200 live registrations, and 0 after those are cancelled (201 entries by list length, one of them the cancelling computation's own) | — | ⚪ no baseline; a same-run pair, and the live count is a count of registrations whose leaf has not completed | `--runtime-cancel` |
| the blocking pool, over 20 000 trivial jobs on 4 workers | submit **1 974–2 655 ns** alone, with the queue kept short by awaiting each job before the next submit; a `spawnBlocking` spawn-and-await round trip **34.7–40.1 µs per job** through the runtime | — | ⚪ no baseline: the pool is new, and neither figure is readable without the job count and pool width its line prints | `--runtime-ops` |
| critical section, notification with nobody parked | 27 ns / 1 ns | — | ⚪ no baseline | `--runtime-ops` |

**The bounded accept path (W14).** `nix develop -c lake exe controls --runtime-service --bound=2` prints a
`servicebench|n=5|bound=2|runUs=…|usPerConn=…|connsPerSec=…` line beside SC14's `service|` record, and the row
above quotes that line across five runs (five further runs of the check, which invokes the mode three times
each, read the same band). It is ⚪ and it is deliberately **not** an accept-throughput figure: the run's whole
wall time is dominated by the staged 100 ms deadline — id 1's response is `Runtime.never`, so its `withTimeout`
fires at ~100 ms — which is why `runUs` reads ~102 ms and `usPerConn` ~20.5 ms for five one-byte connections. The
three numbers are exactly what the mode computes (`runUs`; `runUs / n`; `n · 10⁶ / runUs`) and what the command
reproduces; nothing here is attributed to admission, and a per-accept cost would need a run with no staged
deadline, which the mode does not offer. `runUs` is printed and never asserted, and this row gates nothing (§1).

Re-measured after the cancellation milestone, the round-trip row above reads **1 369–1 394 ns** across three runs
against its recorded 1 042 ns: a 31% delta, at the edge of this document's ±30% band, marked as a cross-revision
pair rather than read as a regression — it compares against the recorded value, and while `--runtime-ops` does print
a stock row in the same invocation, no re-measured stock figure is quoted beside it here.

Three of these rows are the interesting ones. The tail row says an idle worker does not have to be a slow one: a task
pushed while others run is picked up promptly. The shared row compares each design under the discipline it
actually needs — ours is single-carrier, so a plain reference is correct and wins; the stock pool cannot drop
its lock, and the same diagnostic shows why (`253 115 of 800 000` increments survive without it). And the timer
row is the one that shows the *async* path is genuinely non-blocking while the blocking path is the hole in §4.

### 3.1 The synchronisation primitives (W6), and the one comparison that is not ahead

`nix develop -c lake exe controls --runtime-sync` prints these on its `syncbench|` line, in one invocation and
never asserted. Each is over n = 2 000 operations: the uncontended lock is n lock/unlock pairs run by one
computation; the contended row is the same n pairs split across two spawned computations, **each pair holding the
permit across a yield** so the two genuinely interleave at the mutex — one finds the permit gone and parks while
the other is in its held section — and the row prints `heldAcrossYield=yes|no` beside the contended figure, the
observation that the interleaving actually happened: a non-parking `tryLock` inside the yielding chains found the
permit already held by the other computation while this one expected to acquire it, and it reads `no`, never
omitted, when it did not; the wake row prices one
release that wakes 16 parked waiters, per waiter; the semaphore rows are n acquires and n releases, uncontended;
the channel rows send n values into a **capacity-n** channel and drain them with n receives — capacity n for n
sends, so the queue reaches its bound only as the last send completes and the send-park path is never exercised —
and pair our per-message
figure with the same n messages through `Std.Sync.Channel` **in the same run**, the run computing the ratio
itself.

| shape | ours | the other one | ours is | source |
|---|---|---|---|---|
| lock/unlock, uncontended | 343–667 ns per pair | — | ⚪ no baseline | `--runtime-sync` |
| lock/unlock, two computations contending (permit held across a yield) | 1 356–2 059 ns per pair | — | ⚪ no baseline | `--runtime-sync` |
| a release waking 16 parked waiters | 628–1 275 ns per waiter | — | ⚪ no baseline: the design's O(w) wake cost, with no earlier mechanism to divide by | `--runtime-sync` |
| semaphore acquire / release, uncontended | 69–135 ns / 67–148 ns | — | ⚪ no baseline | `--runtime-sync` |
| a message through our bounded channel (capacity n with n sends, so it never fills and the send-park path is not priced) | **275–919 ns** | `Std.Sync.Channel`, same run: **187–531 ns** | 🔴 **~1.3–2.3× worse** on the typical run; the run's own `chanRatioPct` reads 44–76 there, and 33–106 across the whole set | `--runtime-sync` |

The lock and semaphore rows are first measurements — the primitives did not exist before W6 — so they carry no
baseline and are ⚪. `nsLockContended` now reads *above* `nsLockUncontended` (1 356–2 059 ns against 343–667 ns
per pair across four runs), the direction the shape predicts: each contended pair holds the permit across a
yield, so one computation finds the permit gone and parks whenever the other is inside its held section, and the
row prices that park and wake on top of the pair. The construction this replaces — two chains of `lock; unlock`
with no yield — ran each chain's whole sequence inside one step, so the two never interleaved and the row priced
two sequential chains plus one spawn and await; its reading fell *below* the uncontended row (140–295 ns), which
nothing predicted. A direct trace of the corrected shape shows the contention: `A-try` is separated from
`A-acq` by the other computation's `B-rel`/`B-try`/`B-acq` records, i.e. A's `lock` found the permit gone and
waited — the case an async mutex exists for. The line carries that evidence itself: its `heldAcrossYield` field
reads `yes` when the yielding chains' `tryLock` probe finds the permit held — the same observation the trace
records — so the row states the interleaving happened instead of inferring it from the shape. The wake row below
— not this one — is where the design's O(w) cost
is priced. The channel row is the one that is
not ahead, and the residual is the task layer rather than the queue. The queue used to be a `List` appended under
the lock — `state.queue ++ [v]`, O(queue length) per send, so O(n²) to fill a capacity-n channel — and it is now a
two-list FIFO with an explicit size, O(1) amortised in both directions. The reading this row replaces was
**9.4–14.3 µs** per message against **246–304 ns** for the stock channel in those same runs, the mode's own
`chanRatioPct` 1–3. After the change the row reads **275–919 ns** ours against **187–531 ns** stock in the same
runs, and what is left of the gap is not the queue: every send and receive is a step with its item and context
bookkeeping and a full mutex transaction, where `Std.Sync.Channel` is a straight promise-based hand-off, and that
per-operation step machinery is the **~1.3–2.3×** the row still reads. The comparison is same-run — both figures
come from one `syncbench|` line, as §1 requires — and the run's own `chanRatioPct` reads 44–76 on the typical run
and 33–106 across the whole set, a spread wider than §1's ±30% because the box was shared while these ran (load
average ~4 on 8 cores, and the lock rows moved up and down with it). At `LEAN_NUM_THREADS=1` the same rows read
**323–904 ns** for ours against **220–540 ns** for the stock channel, the ratio in the same band; the invocation is
the one in §6.

### 3.2 The handle registry (W12)

`nix develop -c lake exe controls --runtime-registry` prints three `registry…|` lines beside SC15's records. The
**local context has no row**, and this is the honest statement rather than an omitted one: `Async.local` is a read
of a field on the immutable `Ctx` a step already holds and `Async.withLocal` is a structure copy, so there is no
operation to time and a row over one would be noise; SC15-O1 is the evidence that the local does what it must.
The three registry rows are over n = 10 000 handles, and each is ⚪ — there is no earlier mechanism to divide by.

| shape | readings | source |
|---|---|---|
| `registrybench\|n=10000\|addUs=…\|drainUs=…\|usPerHandle=…` — 10 000 handles registered (`Registry.spawn`/`add`, each spawn a computation that has already finished) and then drained: the add path (one `Std.Mutex` critical section + a **cons**, and the 10 000 spawns that precede it), the drain path (one take + 10 000 awaits whose cells are already resolved), and the per-handle share of the drain | addUs **14 780 / 15 039 / 14 548 µs**; drainUs **1 950 / 1 919 / 1 061 µs**; usPerHandle **195 / 191 / 106** (the mode's `benchDrainUs / n`, from its nanosecond timer, so this reads nanoseconds per handle) across three runs | `--runtime-registry` |
| `registryhand\|n=10000\|us=…` — the same 10 000 handles awaited from a bare `List` by hand (the `serveNJoin` shape): the control that says the registry costs only the lock | **1 359 / 1 529 / 1 001 µs**, same three runs | `--runtime-registry` |
| `registryheld\|k=4\|drainUs=…` — a drain over 4 outstanding handlers released after the drain begins: the drain's cost when it actually waits (scheduling, not a lock) | **112 / 97 / 58 µs**, same three runs | `--runtime-registry` |

At one pool thread — `LEAN_NUM_THREADS=1 nix develop -c lake exe controls --runtime-registry`, the invocation
§3.1's precedent uses, since the registry is single-carrier code and the figure must not be read as a scaling
claim — the same rows read addUs **13 811 / 15 172 / 13 798 µs**, drainUs **941 / 1 400 / 968 µs**,
usPerHandle **94 / 140 / 96**, `registryhand` **863 / 1 235 / 859 µs** and `registryheld` **69 / 36 / 56 µs**.

The dominant figure is `addUs`, and this milestone's change is what the row was there to expose: `Registry.add`
appended with `++`, O(queue length) per add in a serving path, so the same 10 000 adds read **553 742 / 560 483 /
545 200 µs** — ~0.55 s, agreeing with the ~532–586 ms this row recorded before the change — against a drain of
about **1.0–1.3 ms**. The
registry has no specified order — a `JoinSet` promises none, and no clause of SC15 reads it — so the cheapest
correct shape is a cons and nothing more: the same 10 000 adds now read **14 548–15 039 µs** (the table above),
roughly the 38× that an O(n²) append costs against an O(1) cons, and **the point of the change is that the add
side stops growing with the backlog**. What remains in `addUs` is not the registry's alone: the path spawns each
handle and then registers it, so it now prices 10 000 spawns plus 10 000 O(1) conses. `drainUs` still prices one
take and 10 000 awaits on resolved cells — about a millisecond for 10 000 handles, the "already there" await cost
and not a lock. `registryhand` is the same await count over a bare `List`, so the gap between it and
`registrybench`'s drain is what the lock and the one take add; `registryheld` is not comparable to either, because
its drain genuinely parks and so prices scheduling a woken continuation rather than a lock. None of the three is
asserted, and none gates anything (§1). The registry's construction and its unbounded membership are
[`decisions.md`](decisions.md) D16 and the module prose.

### 3.3 Selection, racing and priority (W7)

`nix develop -c lake exe controls --runtime-select` prints four `…bench|`/`priorityorder|` lines beside SC16's
records. All are over n = 2 000 rounds except `prioritybench` (100 rounds), and each is ⚪ — the operations did not
exist before this milestone, so there is no earlier mechanism to divide by. Each is nevertheless a same-run pair
with its own `awaitUs` baseline, which is the comparison the workplan names: a selection's and a race's cost
against a plain await.

| shape | readings | source |
|---|---|---|
| `selectbench\|n=2000\|selectUs=…\|awaitUs=…` — 2 000 rounds of `select` over two handles whose cells are already resolved, against 2 000 plain `Async.await`s on a resolved handle, in one run: `select`'s cost against a plain await, including the shared cell's registration loop (which short-circuits in-step here) | selectUs **2 286 / 2 476 / 2 714 / 2 722 µs** against awaitUs **1 149 / 1 321 / 1 605 / 1 618 µs** across four runs (≈1.1–1.4 µs per `select`, ≈0.6–0.8 µs per await); at `LEAN_NUM_THREADS=1` selectUs 2 788 µs against awaitUs 1 601 µs | `--runtime-select` |
| `racebench\|n=2000\|raceUs=…\|awaitUs=…` — 2 000 rounds of `race` over a resolved winner against a parked loser, each round spawning the loser, awaiting its start and cancelling it, against 2 000 plain awaits on a resolved handle: the race's cost against a plain await, *including the loser's cancellation and the loser's own spawn* | raceUs **113 871 / 127 662 / 128 943 / 137 594 µs** against awaitUs **836 / 1 048 / 1 071 / 1 117 µs** (≈57–69 µs per race round against ≈0.4–0.6 µs per await); at `LEAN_NUM_THREADS=1` raceUs 88 726 µs against awaitUs 873 µs | `--runtime-select` |
| `priorityorder\|k=4\|normalThenHigh=…\|highThenNormal=…\|servedBeforeHigh=…\|servedBeforeNormal=…` — the served label order for a `.normal`-then-`.high` issue and the reverse, and how many of the 4 preloaded ring tasks were served before the fresh task's first step, high vs normal: the order the argument changes | `normalThenHigh=high,normal`, `highThenNormal=high,normal`, `servedBeforeHigh=0`, `servedBeforeNormal=4` — identical in every run | `--runtime-select` |
| `prioritybench\|n=100\|k=4\|highUs=…\|normalUs=…` — enqueue-to-first-step for a `.high` and a `.normal` spawn with the ring preloaded with 4 parked tasks (100 rounds each) | highUs **19 622 µs** against normalUs **18 964 µs** in one default run; at `LEAN_NUM_THREADS=1` highUs 9 660 µs against normalUs 9 739 µs — the two lanes do not separate outside §1's ±30% drift, the expected reading, since placement decides *which* preloaded task goes first, not how long enqueuing one costs | `--runtime-select` |

**What each row is evidence for, and where a row's halves are not comparable.** `priorityorder` is the ordering
evidence: the stable `servedBeforeHigh=0` / `servedBeforeNormal=4` pair the scenario asserts, printed a second
time as a measurement, so its meaning does not depend on the machine — this is where the placement is visible.
`prioritybench` is deliberately expected to read flat (`highUs ≈ normalUs`, the difference inside §1's ±30% drift):
the lanes change *which* handle is served first, not *how many* are served, so throughput is expected to be the
same for both. A reader should not look for a benefit in `prioritybench` and should not read the flat pair as the
feature not working — the benefit is `priorityorder`'s `servedBefore*` pair, and `prioritybench` is only the
statement that choosing a lane does not cost throughput.

`selectbench` prices the shared-cell machinery against a bare await; the gap is the registration loop plus the
extra cell the `select` step parks on. **`racebench` is the row whose two halves are not comparable, said plainly
rather than left to the arithmetic.** Per round, `raceUs` includes the **loser's spawn** (a whole computation and
the scheduling of its first step), an **await of the loser's readiness gate**, and the **race itself** (select plus
the loser's cancellation and registration retire); the `awaitUs` baseline spawns nothing and awaits an
already-resolved handle. The ~100× gap is therefore mostly the loser's spawn and its lifecycle, **not** the race's
decision — so the row is ⚪ and is not evidence that selection is two orders of magnitude more expensive than an
await. It is what the command reproduces, and a like-for-like baseline — a row spawning and awaiting the same
handles in the race's shape — is deliberately not offered.

No row is asserted, and none gates anything (§1).

### 3.4 The runtime handle, metering and a signal-driven drain (W13)

`nix develop -c lake exe controls --runtime-handle` prints three `…bench|`/`…cost|`/`…drain|` lines beside
SC17's records. Each is ⚪ — the handle, the counters and the signal-driven stop did not exist before this
milestone, so there is no earlier mechanism to divide by.

| shape | readings | source |
|---|---|---|
| `handlebench\|n=200\|spawnUs=…\|wakeUs=…` — 200 `Handle.spawn`s from a non-carrier thread against a carrier parked, against 200 carrier-side `Runtime.spawn`s in the same run: the cross-thread wake against the same-thread enqueue | spawnUs **7 / 8 / 9 / 9 / 13 µs**, wakeUs **2 / 2 / 2 / 2 / 3 µs** across several runs (both are the row's own `spawnNs`/`enqNs` divided by `n`, in microseconds) | `--runtime-handle` |
| `metricscost\|n=10000\|rounds=5\|meteredUs=…\|plainUs=…\|meteredMaxUs=…\|plainMaxUs=…` — the same program, item count and executor construction in both arms, one arm `Executor.newMetered`, over 5 rounds in one invocation with the order alternated (M,P,P,M,…), reporting each arm's **minimum** with its band beside it: what the counters cost the item path | minima (µs), metered / plain, over six runs: **61 237 / 57 700**, **49 648 / 32 980**, **71 687 / 53 918**, **62 257 / 36 196**, **71 113 / 51 208**, **66 893 / 36 188**; per-arm maxima **89–142 ms** | `--runtime-handle` |
| `signaldrain\|pollMs=1\|stopToDrainUs=…\|accepted=1\|offered=2` — from the handler's step recording the stop to the serving loop's drain returning, live and printed for the reason SC10's `drainUs` is: the poll interval bounds it | stopToDrainUs **317 / 387 / 409 / 537 / 626 / 984 µs** across six runs, with `accepted=1` and `offered=2` in every run | `--runtime-handle` |

**`handlebench` is ⚪ and same-run.** Both figures come from one invocation: the `spawnUs` half is the
non-carrier→carrier wake with the carrier parked, the `wakeUs` half is the carrier-side enqueue, and the pair is
the cross-thread against the same-thread route. The two are not equal by design — one crosses a thread and takes a
lock the other does not — and neither is asserted.

**`metricscost` has a stated direction, and it is the design's.** Metering *adds* work — two `now` reads and one
critical section per item — and removes none, so the expected reading is `meteredUs ≥ plainUs`. Taking the row as a
single non-interleaved pair of 53–70 ms totals on a box whose own §4.7 puts run-to-run drift at ±30% produced a
24% reversal at `n = 10000` that the instrument could not attribute, so the row is taken interleaved instead: the
same program and item count in both arms, the order alternated, and each arm's minimum reported with its band
beside it. At the minima `meteredUs ≥ plainUs` in **every** run, which is the design's direction and the reason
the earlier single-pair reading was withdrawn; but each delta (≈3.5–31 ms over a 33–72 ms baseline) lies inside
the per-arm band (max − min ≈ 50–110 ms), so the row claims the **sign** and no magnitude, exactly as §1 requires.
A reversal surviving the interleaved minima would have been a fixture defect — the arms differing in work — and it
did not survive.

**`signaldrain`'s band is part of the reading.** 317 µs to 984 µs for the same event on the same box, because the
serving loop polls at 1 ms and the stop is noticed on whichever poll follows it; so the figure is a poll-interval
bound and not a latency claim, and the row says so rather than quoting one number.

**There is deliberately no row for the harness clock.** A virtual instant is not a duration: the harness clock's
claim is SC17-O3's assertion (an elapsed reading equal to a stated instant), which is a property, not a
measurement, and `--runtime-handle` prints no timing for it. The busiest of the three rows is `metricscost`,
whose arm difference the band nearly swallows — which is the honest statement of what this instrument can resolve
here.

## 4. 🔴 Where we are worse

Stated before anything above it, because it is the honest part of this document. Three rows carry no factor: the
§4.1 row is now **parity** — W4's blocking pool is what moved it, and the residual below is what remains — one
has no baseline to divide by yet, and one is about the instruments rather than the runtime. Each multiplier is
same-run, like every other in this document, and the subsections below explain the mechanism rather than repeat
the arithmetic.

| worse, and where it comes from | ours | baseline | leanin is | source |
|---|---|---|---|---|
| blocking work, on a carrier or through the pool (§4.1) | 25 767 µs through the pool | stock pool 25 146 µs | ⚪ parity: W4's blocking pool moved it from 🔴 4.0× worse; a blocking call that does not take the pool still stops everything | `--runtime-bench` |
| no core parallelism at all (§4.2) | 1 distinct thread for 64 tasks | — | ⚪ no baseline yet: structural until W8 | `--runtime-bench` |
| a burst submit into an undrained pool (§4.3) | 830 ns | 41 ns of lock, state copy and enqueue | 🔴 **20× worse** | `--runtime-unit` |
| a burst spawn into an undrained pool (§4.3) | 2 730 ns | the same 41 ns | 🔴 **67× worse** | `--runtime-unit` |
| the submit burst against steady state (§4.4) | 951 ns, one transaction | 339 ns, which is two | 🔴 **2.8× worse** | `--runtime-ops` |
| a ring push whose array is shared (§4.5) | 121 ns | 6 ns, the same push uniquely held | 🔴 **20× worse** | `--runtime-unit` |
| carriers added to a serial client (§4.6) | 1 worker: 10 795 µs | 4 workers: 7 988 µs | 🔴 **1.35×, then flat** | `--runtime-async` |
| what the instruments can resolve (§4.7) | ±30% run-to-run | — | ⚪ no factor: a limit of the measurement, not of the runtime | all of the above |

### 4.1 Blocking work stops everything, unless it takes the pool

```
4 x 25ms sleeps      : stock 25146us / leanin 25767us
64 spawned tasks     : 1 distinct threads
```

Four tasks that sleep with `IO.sleep` take **25.8 ms** on our runtime against **25.1 ms** on the stock pool —
parity, both ≈25 ms, where before W4 the row read 100 ms here because the four sleeps serialised on the one
carrier. The sentence this subsection used to carry — "the row should become ~25 ms once blocking work can
leave the carrier" — is now the record of what happened: W4's blocking pool is the change, and
`--runtime-bench`'s shape 2 routes each sleep through `Runtime.spawnBlocking`, so the four overlap off the
carrier exactly as they do on the stock pool's eight workers. The ~2.5% by which the pool-backed reading sits
above the stock row is inside §1's ±30% drift and is not attributed. What is *not* fixed is a blocking call
that does not take the pool route: a leaf that blocks on the carrier still stops everything, which is the
residual this subsection keeps — the pool is a route blocking work must take, not a change to the carrier. The
`64 spawned tasks : 1 distinct threads` line stays, as the vacuity control for "one carrier"; the pool's own
cost is the blocking-pool row in §3, and its effect on the queued workload is the `blockqueue` lines in §5.

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

## 5. ⚪ Rows that are about a pool, not about us

These appear in the same diagnostics — Lean's pool's starvation shape, W4's blocking pool beside it, and the
one escape Lean offers from the stock pool. They are not comparisons with this runtime's scheduler, and they
should not be read as such:

```
queue      : 8 workers blocked 300ms; 8 further tasks finished at 300229us
blockqueue : 8 pool jobs of 300ms on 8 workers; last finished at 300883us
blockqueue : 8 pool jobs of 300ms on 1 workers; last finished at 2401532us
dedicat    : 10000 dedicated tasks, one thread each, ran in 476336us
```

`queue` is the stock pool's starvation shape — with all eight workers blocked, ready work does not run at all.
`blockqueue` is the *same* 8 × 300 ms workload with the blockers routed through W4's blocking pool, at a pool
width printed on each line: at eight workers the work queued behind the blockers finishes about a blocker
later, and at one worker it serialises again (8 × 300 ms), so the two lines are a same-run pair and the
movement is the pool's width, from `W×d` to `d`. It is the same reading under `LEAN_NUM_THREADS=1` as under the
default — 301 411 µs against 300 883/301 050 µs at eight workers — because the blockers are no longer on the
stock pool at all. `dedicat` is the only escape the stock pool offers: `Task.Priority.dedicated` gives a task
its own OS thread, which is one thread per task rather than a bounded blocking pool — the per-job price the
blocking-pool row in §3 avoids by reusing threads. It carries no baseline, and on the W4 re-run it read
746–773 ms against the 476 ms recorded above, so it is a drifting machine fact rather than a comparison — this
record is not updated for it.

## 6. Reproduce

| command | what it measures |
|---|---|
| `nix develop -c lake exe controls --runtime-bench` | the two server shapes: 10 000 tasks spawn+join (native, leanin, `Std.Async`) and 4 × 25 ms blocking sleeps routed through the blocking pool; plus the thread count our tasks ran on |
| `nix develop -c lake exe controls --runtime-async` | that workload swept over worker counts, with a no-body control, and the `Std.Async` row; also the one to run under `LEAN_NUM_THREADS=1` and `8` |
| `nix develop -c lake exe controls --runtime-ops` | per-operation costs: enqueue, take, a spawn+await round trip, a critical section, a notification, a reference pair; plus the blocking pool's submit alone and a spawn-and-await round trip through it, over 20 000 jobs on 4 workers |
| `nix develop -c lake exe controls --runtime-unit` | one transaction decomposed: plumbing, pool operations, and the ring's array sharing |
| `nix develop -c lake exe controls --runtime-tail` | how late the last of 10 000 tasks starts, the stock pool's starvation shape, the same 8 × 300 ms workload in the blocking pool at two widths, and the dedicated-thread shape |
| `nix develop -c lake exe controls --runtime-shared` | the same counter under each design's required discipline, and what the stock pool loses without its lock |
| `nix develop -c lake exe controls --runtime-sleep` | four 50 ms libuv timers on one carrier — 51 ms, against 200 ms for a serial sleep path |
| `nix develop -c lake exe controls --runtime-net` | 16 concurrent echo connections on one carrier: the connection count, the server's thread count, whether the client shares it, the byte-identical replies, and the pool alongside |
| `nix develop -c lake exe controls --runtime-service --bound=2` | the bounded accept path (SC14): one 5-connection run's wall time, its per-connection share, and the connections/s that implies — the figures §3's service row quotes — plus SC14's `service\|` record and its checker's `servicectl\|` readings |
| `nix develop -c lake exe controls --runtime-time` | 16 × 50 ms sleeps and their event order, two timeout outcomes, the task layer's first-writer law, and the blocking path for the same sleeps |
| `nix develop -c lake exe controls --runtime-drain` | a stop with a connection in flight: whether the connection completes after the stop, whether the pool is empty and whether a leaf registration is outstanding when the run returns, and how long the drain takes |
| `nix develop -c lake exe controls --runtime-cancel` | a disconnect cancelling the work: the counter as it stood in the cancelling step and after the run returns, the work's own registrations before and after, the cancelled handle's outcome, and a second cancellation; plus the cost of the new operation — spawn-and-await against cancelling a parked task — and the registry's size before and after cancelling 200 parked awaits |
| `nix develop -c lake exe controls --runtime-sync` | the sync primitives' cost (§3.1): lock/unlock uncontended, and contended with the permit held across a yield — the row printing `heldAcrossYield=yes\|no` from the yielding chains' own `tryLock` probe — a release that wakes 16 parked waiters, the semaphore's acquire and release, and a message through the bounded channel beside the same message count through `Std.Sync.Channel` in one run; plus SC13's `sync\|` record and its checker's `syncctl\|` readings |
| `LEAN_NUM_THREADS=1 nix develop -c lake exe controls --runtime-sync` | the same `syncbench\|` rows, and the invocation §3.1's `LEAN_NUM_THREADS=1` channel figures come from — the stock channel beside ours at one pool thread |
| `nix develop -c lake exe controls --runtime-registry` | the handle registry's cost (§3.2): 10 000 handles registered and drained, the same count awaited from a bare `List` as the control, and a drain over 4 outstanding handlers released after it begins; plus SC15's `context\|` and `registry\|` records and its checker's `registryctl\|` readings |
| `LEAN_NUM_THREADS=1 nix develop -c lake exe controls --runtime-registry` | the same `registrybench\|`/`registryhand\|`/`registryheld\|` rows at one pool thread — the invocation §3.2's one-thread figures come from, since the registry is single-carrier code and the figure is not a scaling claim |
| `nix develop -c lake exe controls --runtime-select` | selection, racing and priority (§3.3): 2 000 rounds of `select` against a plain await, 2 000 rounds of `race` (each round spawning, awaiting and cancelling a parked loser) against a plain await, the served label order for a `.normal`-then-`.high` issue and the reverse with the preloaded-ring counts, and enqueue-to-first-step for both lanes; plus SC16's `select\|`, `race\|` and `priority\|` records and its checker's `selectctl\|` readings |
| `LEAN_NUM_THREADS=1 nix develop -c lake exe controls --runtime-select` | the same `selectbench\|`/`racebench\|`/`priorityorder\|`/`prioritybench\|` rows at one pool thread — the invocation §3.3's one-thread figures come from, since the runtime is single-carrier code and the figures are not scaling claims |
| `nix develop -c lake exe controls --runtime-handle --ready-file PATH` | the runtime handle, the counters and a signal-driven drain (§3.4): 200 non-carrier `Handle.spawn`s against a parked carrier beside 200 carrier-side spawns; the metered and unmetered accumulators over 5 alternated rounds (minima and band) on the same program; and the signal-to-drain return. Started as a background executable and sent `SIGTERM` at the pid it writes to `PATH`, like `tests/executor-contract.sh SC17`; it also prints SC17's `handle\|`, `clock\|`, `signal\|`, `tokens\|` records and its checker's `handlectl\|` readings, and no timing for the harness clock (a virtual instant is not a duration) |

## 7. What these numbers are not

- **Not a gate.** They are printed, never asserted: a timing assertion is a flake with a schedule.
- **Not evidence about correctness.** That is SC1–SC6 at the executor boundary, the model's obligations, and
  the controls in `docs/evidence.md`.
- **Not a comparison with Tokio.** None runs here; the Rust reference copy is for the algorithms.
- **Not a claim about a different machine.** Same toolchain, same box, `nice -n 19`.
