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
the channel pair sends n values into a **capacity-n** channel and drains them with n receives — capacity n for n
sends, so the queue reaches its bound only as the last send completes and the send-park path is never exercised —
and pairs our per-message
figure with the same n messages through `Std.Sync.Channel` **in the same run**, the run computing the ratio
itself.

| shape | ours | the other one | ours is | source |
|---|---|---|---|---|
| lock/unlock, uncontended | 343–667 ns per pair | — | ⚪ no baseline | `--runtime-sync` |
| lock/unlock, two computations contending (permit held across a yield) | 1 356–2 059 ns per pair | — | ⚪ no baseline | `--runtime-sync` |
| a release waking 16 parked waiters | 628–1 275 ns per waiter | — | ⚪ no baseline: the design's O(w) wake cost, with no earlier mechanism to divide by | `--runtime-sync` |
| semaphore acquire / release, uncontended | 69–135 ns / 67–148 ns | — | ⚪ no baseline | `--runtime-sync` |

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
is priced. The channel comparison is the one that is
not ahead — its row is carried in §4.8, so that this section holds only rows we win and rows that are not
comparisons at all — and the residual is the task layer rather than the queue. The queue used to be a `List`
appended under the lock — `state.queue ++ [v]`, O(queue length) per send, so O(n²) to fill a capacity-n
channel — and it is now a two-list FIFO with an explicit size, O(1) amortised in both directions. The reading
this row replaces was **9.4–14.3 µs** per message against **246–304 ns** for the stock channel in those same
runs, the mode's own
`chanRatioPct` 1–3. After the change the row (§4.8) reads **275–919 ns** ours against **187–531 ns** stock in the same
runs, and what is left of the gap is not the queue: as the `chanunit|` decomposition in §4.8 prices, it is a full
mutex transaction whose waiter-list sweep is paid on every operation, plus the CPS closure chain the operation is written in,
where `Std.Sync.Channel` is a straight promise-based hand-off — not the item-and-context bookkeeping a step
carries, which that row prices at **~22 ns** and which is not incurred per message at all. The comparison is same-run — both figures
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

### 3.5 P carriers: the batch shape, the chain, and a driven steal (W8)

Three rows `--runtime-carriers` prints, beside the SC18 records, all **printed and never asserted** (§1: a
timing assertion is a flake with a schedule).

```
parbatch|p=1|n=500|leaninUs=9168|nativeUs=16957|ratio=54|nativeThreads=8|cores=8
parbatch|p=2|n=500|leaninUs=6305|nativeUs=17372|ratio=36|nativeThreads=8|cores=8
parbatch|p=4|n=500|leaninUs=5277|nativeUs=18014|ratio=29|nativeThreads=8|cores=8
parbatch|p=8|n=500|leaninUs=4942|nativeUs=18335|ratio=26|nativeThreads=8|cores=8
parbatchcond|pMin=1|pMax=8|ratioMin=54|ratioMax=26|margin=half|met=yes|...
chain|construction=Async.spawn/await, per-link tid record|links=2000|leaninNs=703|nativeNs=6966|ratio=9.90|chainCarriers=1
chain|construction=Async.spawn/await, no per-link instrumentation (recorded shape)|links=2000|leaninNs=832|nativeNs=6966|ratio=8.37|chainCarriers=n/a
stealbench|n=765|stealNs=307|localTakeNs=320|victimsScanned=2
carriers|carriers=4|p=4|...|distinctCarriers=4|carrierCount1=1|chainCarriers=1|parkedBefore=4|...|remaining=0
```

`--runtime-carriers --workers 4`, one invocation on an eight-core box at load average 2.2; the native
calibration from the same tree in the same window is `ops: native Task spawn+join 6100 ns`. The
`--workers 8` invocation runs the same rows (`parbatchcond|met=yes`, ratios 50 → 24; chain recorded shape
7.77×, `chainCarriers = 1`; `carriers=8`).

**The batch shape, and its condition.** `parbatch|` is a CPU-shaped batch (a fixed arithmetic loop, its result
printed as a checksum so neither arm can be elided) swept over `p = 1, 2, 4, 8`, each arm beside the native
pool's own figure taken in the same invocation. The claim is the **endpoints**: `ratio(p_max)` against
`ratio(1)`, margin a halving, and the interior arms are reported and expressly *not* asserted between their
neighbours (four points at §1's ±30% cannot resolve a monotone path). Here `ratio` falls 66 → 31, a fall of
more than half, so `parbatchcond|met=yes`. **A regression** is `ratio(p_max) ≥ ratio(1)`, a shrink the printed
bands swallow, or a reversal that does not survive the interleaved minima at a raised `n`. Scope: our arms are
capped at `min(8, cores)` and the native pool's width is a fixed configuration printed on the row, so a `ratio`
reads ours-at-`p` against a fixed native pool, not a same-width scaling.

**The chain, and its condition.** `chain|` is a dependent chain of `Async.spawn`/`await` links, ours beside a
native `Task` chain in the same invocation; the ratio is a multiplier (`nativePerLinkNs / leaninPerLinkNs`) and
the row names the construction. **Only the un-instrumented arm is the recorded shape** (a spawn+await per link);
the instrumented arm's per-link tid record is quadratic and is printed to show it. On the recorded shape ours
reads **1307 ns** per link (within the band recorded around 924–1394 ns) against native **10806 ns**, a
**ratio of 8.26×**, with `chainCarriers = 1`. **A regression** is `leaninPerLinkNs` rising into the native
row's band, or a `ratioX` below the base revision's own same-session ratio (per step 3b, ≈4.3× on the reading
that settled it — the doc's 5.3× and the workplan's historical 7.6× are the same shape at other revisions and
are stamped as history, not used as constants).

**The constructions, named, because the route rebinding changed what `chainCarriers` is a claim about.** Before
it (D19) a link's continuation closed over the *awaiting* step's route, so a chain whose link was flushed to the
inject by the LIFO allowance still returned to the carrier that *created* it: `chainCarriers = 1` was that
captured-route artifact, not a property of the chain. After it (D22) a link is pushed on the route of the worker
that *resolves* it, so a chain follows the worker that fires each link and `chainCarriers > 1` is legitimate
rather than a regression — the allowance's own flush (measured on this row's chain as roughly one flush per two
links, D21) can hand a link to another carrier, and the chain follows it. **`chainCarriers` is therefore a
consequence of the scheduler's choice and not a criterion**: the row states the count it read, and which
construction it read it on. W8's LIFO milestone criterion 2 (`chainCarriers = 1` on *that* milestone's arm) is
re-read as the pre-rebinding construction's identity (`w8-lifo-bound/PLAN.md`), and nothing here re-baselines it.

```
session: 8 cores, kernel 6.17.0-1032-oem, load average 2.0–3.3, both trees interleaved in one command
chain|construction=Async.spawn/await, per-link tid record|links=2000|leaninNs=819|nativeNs=8165|ratio=9.96|chainCarriers=1
chain|construction=Async.spawn/await, no per-link instrumentation (recorded shape)|links=2000|leaninNs=810|nativeNs=8165|ratio=10.08|chainCarriers=n/a
carriers|carriers=4|p=4|…|distinctCarriers=4|carrierCount1=1|chainCarriers=1|parkedBefore=4|…|remaining=0
```

**The two readings are one construction, one session.** The rows just given were taken in one W18 session, so
they are comparable to each other and to the band above (ours 810–819 ns per link against the recorded 1307 and
the 924–1394 band; ratio 9.96–10.08 against 8.26). The count is a reading rather than a control: the arm starts
its `p` carriers, so a crossing is *possible* there, and a run that reads 1 records the scheduler's choice, not
a requirement — which is why W18's contract had to stop asserting it.

**The other construction, priced by its own record and not by this row.** The chain the rebinding makes visible
— one link delivered through the shared route whose continuation is deferred onto a *parked* carrier's own queue
— is `SC22`'s completion arm (`tests/executor-contract.sh SC22`), whose record reads `crossed = 1` with every link
run once, `waiterParked = 1` and `heldAfterStop = 0`; it is not comparable to the row above (its links are not a
spawn/await chain running on one carrier), so it is quoted as a behaviour and never as a multiplier.

**The driven steal.** `stealbench|` prices one driven steal against a local take, and **the pair is not
like-for-like and the row says so**: `stealNs` (466) is the driven steal alone while `localTakeNs` (486) is the
whole take path including its steal attempt and the inject check. ⚪ no baseline exists, so the row has no
regression definition.

**The take path, measured, and its one recorded regression.** The `--runtime-ops` round trip is the
*localising* instrument step 3b/c used, not the `chain|` row, and it is the one row in this milestone that
does **not** meet its criterion. Taken interleaved against the base revision in the same session (base = the
committed tree, a scratch export; balanced AB/BA, minima per §1):

```
native Task spawn+join   base ~5956–7205 ns   current ~5721–6534 ns
spawn+await round trip   base  1540–1685 ns    current 2210–2252 ns
same-session ratioX      base  ~3.9–4.3×        current ~2.6–2.9×
```

So the take path does not return to the base's same-session ratio. What it *was*: the take's spent-allowance
arm (flush the LIFO slot to the shared list, then fetch it back) ran on **every** take after three, because
nothing refreshed the allowance — the LIFO slot is otherwise dead for the rest of the run, which is also why
the chain-shaped rows moved. Two repairs landed. The first had the allowance refresh **inside the take's own
transaction** (so the spent-allowance arm runs once per allowance rather than on every take, and the extra
fetch is paid once per allowance) — **and it was taken back, because it made the allowance per-chain**: the
slot was served for as long as its owner kept refilling it, which starved ring-resident work behind a spawn
chain. The bound is now per-tick again, with `lifoPolls` counting *consecutive* slot polls and refreshed by any
decision that is not a slot serve, folded into `Pool.takeReport` so both take spellings read one transaction.
The three arms, re-measured interleaved against the plan's own definitions with the take path's refresh removed
as arm C and the base as arm B (the earlier session's log is not on disk; these are the reviewer's independent
run, same session, minima per §1):

```
arm A (fixed)              2346 ns                       435 ns
arm B (base, f5e6c9d)      1851 ns                       333 ns
arm C (refresh removed)    2510 ns                       705 ns
```

**A beats C on both** (−6.5% round trip, −38% spawn+take), which is criterion 1's direction and its instrument;
**A is above B on both** (+27%, +31%), which is the bound's price and criterion 4's finding. The chain row's
A-vs-C half is **unmeasured**: that pair first read at mismatched carrier counts (arm C at four, arm A at one),
and the re-measurement labelled its "C" arm with a tree byte-identical to the base, so no figure is claimed for
it — the row is recorded as measured against B, not C, and it carries no criterion.

The historical note that follows — the W8-era repairs and their figures — stands as that milestone's record.
What changed after it: the refresh **inside the take's own transaction** was taken back, because it made the
allowance per-chain and starved ring-resident work behind a spawn chain. The bound is per-tick again, with
`lifoPolls` counting consecutive slot polls and any non-slot decision refreshing it, folded into
`Pool.takeReport`; the take row's own figures below are from the W8 window and are **not** re-taken here. What
that change did to the two condition-2 instruments is in the table above: `--runtime-ops` puts the fixed build
below the pre-repair shape (criterion 1's direction), and the `chain|` half is **unmeasured** — no figure is
claimed for it.
So the sentence below about the second condition not being met by the `--runtime-ops` instrument describes the
pre-repair state, not this one; the honest current statement is criterion 3's recorded miss on the chain ratio
**(A 8.07–8.52 against B's same-session 9.00–11.26)** with its attribution — the fixed build flushes 1001 times
over the chain run against B's 1 and the pre-repair shape's 3997, one flush per two links — its native-pool
advantage intact and three levers named for the user rather than pulled.

What remains from it: the hot take and push paths are `@[inline]` (the body's cost is one pool transaction,
and a call boundary there cost as much as the transaction outright — measured: the same body inlined is ~380 ns
against ~760 ns called). Those repairs moved the take row from 555 ns to **92 ns** and `spawn+take`
(steady) from 1407–1683 ns to **442 ns** — at or below the base's 488 ns — and the round trip from ~3524 to
**2205 ns** (native 6100 ns, `ratioX` ≈ 2.77 in that window). **The enqueue-side gain W8 gave back is now
recovered, and measured rather than assumed.** W8's record priced the per-worker wake flag at `Executor.spawn`
**466 ns against 372–389 ns with the bit removed**. W18 removes the flag (the third off-owner local push it
covered no longer exists), so the row is re-taken **interleaved against the base revision in one session** — base
= the committed tree at `01dcb3b`, a `git archive` export beside the working tree, balanced AB/BA, **four runs
an arm, minima per §1** — at 8 cores, kernel 6.17.0-1032-oem, load average 2.6–3.3 through the session:

```
Executor.spawn      base (bit standing)  335 331 359 385     min 331 ns
                    fixed (bit gone)     295 287 289 296     min 287 ns
spawn+await round   base                1906 2412 2047 2411  min 1906 ns
                    fixed               1850 2169 2224 1905  min 1850 ns
native spawn+join   base 5312–6638 ns    fixed 5317–7989 ns  (calibration, same session)
```

So the bit's price is **44 ns** in this session, in the direction W8 stated; the fixed tree's absolute
287–296 ns is at or below the stated bit-free band (372–389 ns), which is a *different session's* level — §1
forbids pairing across sessions — so the recovery is claimed from the interleaved pair rather than from that
band. The round trip is **not regressed** by the delivery change: the deferred continuation now builds a
`Join.Waiter` and an `Item.ofDeferred` and re-binds a context at fire time, and the row still reads at or below
the base's own same-session minimum. The paragraph above is W8's record of the tree *before* this milestone and
is left as history; these rows are W18's on the same instrument. **The residual is the split's own per-operation overhead** — the per-worker cell and its placeholder
on every transaction, the `TakeReport`-shaped decisions the records need, and the `Sendable` marker on every
crossing — and it is recorded here rather than absorbed: the second measurement condition's criterion is the
base's same-session ratio, and it is **not met** by the `--runtime-ops` instrument. Per the plan's own rule, a
take whose cost is inherent to where the decision now sits rather than a mistake in it is a finding for the
planner and the user, not a re-baselining — and this is that finding. The `chain|` row above, which is the
plan's §6 condition-2 measurement, reads green; the two instruments disagree because they price different
constructions (a 2000-link chain pushed off-carrier against a 20000-link round trip driven on the calling
thread), and both readings are recorded rather than one chosen.

### 3.6 Owning the HTTP/1.1 parser: 10× on the parse, invisible at one connection

`Std.Http.Protocol.H1`'s parser is a `Parsec` combinator parser: it converts every token it scans back into a
`ByteArray` and then a `String`, tries the method against ~40 `attempt`-wrapped alternatives, and re-allocates a
`"\r\n".toUTF8` literal on every line. `LeanIn.Http.H1` replaces it. The method is dispatched on its first byte;
the request target and every header name/value stay a `Slice` — a pair of indices **into the read buffer that was
already allocated** — so the head parse copies nothing per token, and only the response is built.

The parse, isolated and driven in-memory for the same request by `h1bench` (compiled exe, no sockets, no timers;
`stdOnce`/`ourOnce` in `H1Bench.lean`), and the same under `callgrind`:

| arm | instructions/parse | ns/parse |
|---|---|---|
| `Std.Http.Protocol.H1` | 70 837 | 6 679 / 6 712 |
| `LeanIn.Http.H1` | **9 040** | **633 / 613** |

**7.8× fewer instructions, 10.8× faster** on the parse itself. `callgrind` puts Std's `scanWhileUpTo` at only
4.3 %, but the parse's real cost is the memory-management column it drives — `lean_dec_ref_cold` 13.2 %,
`mi_free` 9.7 %, `lean_alloc_small_object_core` 6.3 % — the allocations the token-to-`String` round trip makes.

**The server cannot see that at one connection.** `server static quiet` driven by `bench/load.mjs` in keep-alive,
same box and session, `maxMessages` bumped on both arms so neither closes mid-run:

| arm | C=1 rps | C=1 p50 | C=4 rps | C=4 p50 |
|---|---|---|---|---|
| `Std.Http.Protocol.H1` | 31 182 / 29 106 | 27 / 31 µs | 28 893 / 30 016 | 132 / 131 µs |
| `LeanIn.Http.H1` | 26 704 / 27 815 | 29 / 30 µs | **45 004 / 53 172** | **81 / 67 µs** |

At C=1 the two are a wash, and that is the reading the runtime's own finding predicts rather than a surprise:
§4.7 already established that a keep-alive request at one connection is **orchestration, not work**, so a parse
seven times cheaper is seven times cheaper on the slice of the path the handoffs dominate, and it lands inside
§4.7's ±30 % run-to-run band. At C=4 the parse's share is large enough to resolve: **1.6× the throughput and
1.7× lower p50**. The parse row is the claim; the C=4 row is what the server instrument can see of it; the C=1
row is recorded as a wash, not claimed as a win.

The behaviour is gated, not measured: `tests/executor-contract.sh SC20` drives the connection through
`LeanIn.Http.Server.serveConn` and compares the wire bytes against a `Std.Http.Protocol.H1.Machine` driven in memory
as an independent oracle — one connection serving two exchanges, a handler failure answered as
`500 Connection: close`, and a stalled peer — so the bytes are checked against the protocol it replaces, not only
against a pinned literal.

Reproduce. Parse and instructions:
`nix develop -c lake build h1bench && ./.lake/build/bin/h1bench` for ns/parse, and
`nix develop -c valgrind --tool=callgrind --callgrind-out-file=/tmp/cg.out ./.lake/build/bin/h1bench 4000`
read with `--inclusive=yes` for the instruction split. Server rows, the binary needing the shell's libraries:
`LD_LIBRARY_PATH="$(nix develop -c printenv LD_LIBRARY_PATH)" ./.lake/build/bin/server <port> static quiet`
driven by `node bench/load.mjs <port> <C> 5 /bench`.

## 4. 🔴 Where we are worse

Stated before anything above it, because it is the honest part of this document. The section holds one
**external comparison that we lose** — a message through our bounded channel against `Std.Sync.Channel`, our
**275–919 ns** against its **187–531 ns** in the same run (§4.8) — and one **external comparison at parity** —
blocking work against the stock pool, which W4's blocking pool moved from 🔴 4.0× worse to a tie and which is
marked ⚪ because a pair that ties attributes nothing either way (§4.1). It also holds the **internal cost
decompositions**, all ⚪: the burst submit and burst spawn (§4.3), the submit burst against our own steady state
(§4.4) and the ring push with the array shared (§4.5) each set this runtime against a narrower arm of itself,
and the structural rows (§4.2, §4.6) and the instrument row (§4.7) are facts about this runtime and these
instruments, or pairs of our own numbers, rather than comparisons at all. Which rows have another
implementation as their baseline and which are against ourselves is readable from the marker and from each row's
own stated reason.

Of the 47 rows in §§2–4, **12 compare us against another implementation and carry a
verdict — 11 🟢 and 1 🔴 — and 35 are ⚪**. Thirteen rows in all have another implementation as their baseline:
those 12, plus the §4.1 parity pair, which is external and ⚪ at once because a tie attributes nothing. The other
34 ⚪ rows are internal: decompositions of our own cost, same-run pairs against ourselves, and facts about the
instruments. (The printed rows in §3.5 and §5 are outside this count.) Each multiplier is
same-run, like every other in this document, and the subsections below explain the mechanism rather than repeat
the arithmetic.

| row, and where it comes from | ours | baseline | leanin is | source |
|---|---|---|---|---|
| blocking work, on a carrier or through the pool (§4.1) | 25 767 µs through the pool | stock pool 25 146 µs | ⚪ **an external comparison at parity**: W4's blocking pool moved it from 🔴 4.0× worse, and a tie attributes nothing either way; a blocking call that does not take the pool still stops everything | `--runtime-bench` |
| core parallelism (§4.2) | 4 distinct carriers at `p=4`, `distinctCarriers=4` | — | ⚪ **not a comparison**: a fact about our own runtime with no baseline to divide by; the structural row is superseded by W8's carriers, whose `parbatch` sweep is §3.5 | `--runtime-carriers` |
| a burst submit into an undrained pool (§4.3) | 586–881 ns | 53–77 ns of lock, state copy and enqueue | ⚪ **not a comparison**: the baseline is our own step's transaction plumbing — the same runtime without the pool — so the ~11× decomposes our own cost rather than measuring us against another implementation | `--runtime-unit` |
| a burst spawn into an undrained pool (§4.3) | 440–792 ns | the same 53–77 ns | ⚪ **not a comparison**, for the same reason: our own plumbing figure again, so the ~10× is a decomposition of our own cost | `--runtime-unit` |
| the submit burst against steady state (§4.4) | 850–894 ns, one transaction | 485–502 ns, which is two | ⚪ **not a comparison**: the baseline is our own steady-state spawn-and-take — one of our transactions set against two of ours — so the ~1.7–1.8× is a decomposition and not a defeat | `--runtime-ops` |
| a ring push whose array is shared (§4.5) | 191–464 ns | 10–16 ns, the same push uniquely held | ⚪ **not a comparison**: the baseline is the same operation under a different ownership discipline — our own ring with the array uniquely held — so the ~20× prices the copy between two arms of our own ring | `--runtime-unit` |
| carriers added to a serial client (§4.6) | 1 worker: 10 795 µs | 4 workers: 7 988 µs | ⚪ **not a comparison**: that client is serial by construction, so the pair is internal; the parallel row is the `parbatch` sweep in §3.5 | `--runtime-async` |
| what the instruments can resolve (§4.7) | ±30% run-to-run | — | ⚪ **not a comparison**: a limit of the measurement, not of the runtime | all of the above |
| a message through our bounded channel against `Std.Sync.Channel` (§4.8) | **275–919 ns** | `Std.Sync.Channel`, same run: **187–531 ns** | 🔴 **~1.3–2.3× worse**: the one external comparison this document loses, same-run as §1 requires; the residual is the per-operation step machinery, not the queue | `--runtime-sync` |

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

`64 spawned tasks : 1 distinct threads` was structural until W8 and is now superseded: `Runtime.runCarriers`
starts `p` dedicated carriers and the parallel arm's work runs on them — SC18-O1's control reads
`distinctCarriers = 1` at `P = 1` and `≥ 2` at `P = 4`, with every ran tid in the started carriers' set. The
row's old form (`--runtime-bench`'s one-carrier client) still reads one thread, because that client drives
`Runtime.run`; the multi-carrier reading is `--runtime-carriers` and is in §3.5.

### 4.3 A burst into an undrained pool no longer grows with the backlog

```
unit: transaction plumbing 61ns | + Pool.submit 695ns | + Pool.spawn 664ns
```

One line from one of nine invocations (`nix develop -c lake exe controls --runtime-unit`, already the best of
two inside each). Across them, on this eight-core box at load average 3.05–4.00 — a shared box; the same tree in
the same window reads `ops: native Task spawn+join 9 602–15 512 ns` — the plumbing row reads **53–77 ns**,
`Pool.submit` **586–881 ns** and `Pool.spawn` **440–792 ns**. The plumbing figure is the lock, the state copy
and the scheduler record: the whole of a transaction that does not touch the pool. Each pool operation adds one
ring placement to it, and the harness loops 20 000 of them through a 256-slot ring with nothing taking, so the
ring is saturated and the overflow arm runs about once per 128 placements. That arm sheds the newer half by
*moving the live count* — `Ring.keepFirst`, nothing copied — and **returns** the evicted half to the caller.
There is no `inject` field here to append it to: the pool is inject-free ("the shared queue is the executor's
cell, not a worker's"), so the append a burst would walk is not in this structure at all. It is the caller's
work, in `Executor.pushItems`, into the shared cell's `Deque`, whose `push` writes at the back of the live range
and rebuilds only when the store is exhausted — **amortised O(1)** where the pool's own `List` append was
O(length). (This harness takes the pool half of each placement, so it prices the pool's own work; the shared
deque's push is what §4.4's `--runtime-ops` burst and the `--runtime-carriers` rows reach.) (**Corrected:** that "amortised O(1)" held only for a uniquely owned store, which the shared cell's never was; see §4.9.) `Pool.spawn`'s row is
where the old cost showed: it read **2 730 ns** against `Pool.submit`'s 830 ns when the overflow appended a
growing list, and reads **440–792 ns** now that it only returns the overflow; `Pool.submit`, whose overflow the
old shape reached on the same saturation, moved less, to **586–881 ns**. Both are burst rows, and the burst rows
are what happens when nothing takes. The figure both divide by — the plumbing row — is our own step's
transaction without the pool, so the ~11× and ~10× decompose our own cost and the rows are ⚪, not a comparison
with another implementation.

### 4.4 The same, seen from one operation

`Executor.submit` sits in the table against `spawn+take (steady)`, and the comparison is deliberately harsh: one
transaction against two — but it is a comparison inside our own runtime, which is why the row is ⚪ and its ratio
decomposes our cost rather than measuring us against another implementation. `Executor.spawn` (**496–517 ns** in
this window) does not show the effect, because it
writes the LIFO slot and only occasionally reaches the ring. Re-taken with `--runtime-ops` in the window §4.3
names (load average 3.5–4.0), the burst submit reads **850–894 ns** against the steady spawn-and-take's
**485–502 ns**, so the one transaction still costs **~1.7–1.8×** the two it is set against — the recorded pair,
951 ns against 339 ns, was the same shape at 2.8× in an earlier window. The burst's own cost is the ring
placement on a saturated ring (the shared-array copy §4.5 prices), not the transaction.

### 4.5 A ring mutation still copies its slots when the array is shared

```
unit: Ring.push unique array 15ns | array shared with a live ring 422ns
```

The copy is 2 KB, and it happens whenever the array is referenced twice. `Executor` now releases the cell's hold
before it modifies the pool, which is where that sharing came from, and the take path asks the scheduler before
it reads the pool — but the row stays in the harness because the effect is easy to reintroduce. Re-taken across
the §4.3 window (load average 3.05–4.00, and 15 further runs at 3.3), the pair reads **10–16 ns** uniquely held
against **191–464 ns** shared, roughly 20× either way; the recorded 6 ns / 121 ns is an earlier window that I did
not reproduce here, and the ratio is what the row exists for. Both arms are our own ring — the same push with
the array uniquely held — so the pair is ⚪ and prices a copy inside our own structure, not a comparison with
another implementation.

**Corrected:** "`Executor` now releases the cell's hold" removed one source of the sharing, not the copy. See §4.9:
a cell another thread has reached copies on every write regardless, and the row's unique arm is not the state a
running carrier's pool is in.

### 4.6 Added carriers no longer read as "no scaling"

The old row — 1 worker 10 795 µs against 4 workers 7 988 µs, "1.35×, then flat" — was the serial client's
in-order `await` loop, which cannot scale however many carriers run, and this document used to say so and then
say there was no second measurement. W8 supplies it: `--runtime-carriers`' `parbatch|` row is a CPU-shaped
batch swept over `p = 1, 2, 4, 8` beside the native pool **in the same invocation**, and its condition is the
endpoints (`ratio(p_max)` against `ratio(1)`) rather than the interior. That row, its regression definition and
its reading are in §3.5.

### 4.7 Measurement itself is a limitation

Not a claim about the runtime, but about the instruments, and it limits what can be claimed at all. There
**is** a paused clock and a deterministic driver — W13 delivered the harness clock (`--runtime-handle`'s
`clock|` rows) — so the old sentence saying there was none is corrected here; what remains is that there is no
ThreadSanitizer in the runtime. Combined with the ±30% drift in §1, small effects cannot be resolved today: the
reorder in `Executor`'s take path was worth 2–8%, which is inside the noise of a single run and needed five
interleaved pairs to see.

### 4.8 The one external comparison we lose: a message through our bounded channel

Against `Std.Sync.Channel`, in the same run: **275–919 ns** ours against **187–531 ns** stock per message, the
run's own `chanRatioPct` reading 44–76 on the typical run and 33–106 across the whole set — a spread wider than
§1's ±30%, because the box was shared while these ran. Both figures come from one `syncbench|` line, as §1
requires of a comparison: n sends into a capacity-n channel drained by n receives, ours beside the same n
messages through the stock channel, with the ratio computed inside the run; at `LEAN_NUM_THREADS=1` the same rows
read **323–904 ns** ours against **220–540 ns** stock. This is the row that makes the section title true — a
comparison with another implementation, and one we lose.

What remains of the gap was previously written as the **per-operation step machinery** — "every send and
receive is a step carrying its item and its context bookkeeping and taking a full mutex transaction". The
decomposition `--runtime-chan` prints in the same construction (`chanunit|`, n = 2 000, in the same run as the
pair above, on this box at load average 3.95–4.35) prices that sentence and does not support it. The step
construction is nearly free: `nsStep` — `Item.ofAction` plus the stamp that fills its token — reads **19–25 ns**
and `nsCtx` — the `Ctx`'s two `BaseIO` closure fields — **1–2 ns**, and both are per *construction*, not per
message: the served run builds a single root `Item.ofIndexed` and one `Ctx` for the whole `2n`-operation
program, so neither costs anything in this row. The park path is not taken either — the capacity-n channel
never fills, as §3.1 records — so the waiter's `Join` is never built (`nsJoinPark`, `Join.new` plus
`Join.onReady`, **134–224 ns per registration**, contributing zero here).

The served message instead decomposes as **574–735 ns** (`nsWhole`, the row's own figure) against the stock
channel's **460–589 ns** in the same run — the 1.06–1.35× (`chanRatioPct` 74–94 there) inside the recorded
band. Of that whole, in
nanoseconds per message:

- **78–92 ns** is the mutual exclusion itself — two bare `Std.Mutex.atomically` transactions (`nsBareTx`),
  consistent with `--runtime-unit`'s plumbing row (61–68 ns) and `--runtime-ops`' mutex section (29–49 ns);
- **200–256 ns** is the served transaction's own state work (`nsServedTx` minus `nsBareTx`), split — by a full
  capacity-1 channel's `trySend`, which runs the served branch's `else`, against a roomy channel's
  `trySend`/`tryRecv` — into the `live`/`prune` walk plus the room check, **92–110 ns** (`nsPruneWalk`), and
  the enqueue or dequeue and the wake, **108–150 ns** (`nsEnqueue`). On this path the two halves are
  comparable, and neither is a few nanoseconds: the enqueue is a cons but each send also copies the
  `ChanState` record twice, and the `sweep` that decides whether a walk is due is paid over two *empty* lists
  even when it walks nothing — which is why this figure is largely fixed cost rather than a walk's cost, and
  why amortizing the walk (see below) left the served row within noise;
- **~120–180 ns** is the CPS closure chain the operation is written in (`nsLoopAsync`, the same program with
  `pure ()` in place of every send and receive), with the served operation's own closure and its call into
  `sendStep`/`recvStep` in the residual between `nsChanWork` and `nsServedTx`.

So the served row's cost is a full mutex transaction whose waiter-list sweep is paid on every operation, plus the CPS closure
chain the operation is written in — not item-and-context bookkeeping, which is zero here. It is not the queue:
the queue was a `List` appended under the lock (`state.queue ++ [v]`, O(queue length) per send, so O(n²) to
fill a capacity-n channel) and is now a two-list FIFO with an explicit size, O(1) amortised in both directions,
which took the row from the **9.4–14.3 µs** ours against **246–304 ns** stock it replaced to the figures above.
The construction, field by field, is §3.1.

**The `live` walk was the park path's quadratic, and it is now amortized.** Parking n waiters cost more than
linearly per waiter, and the cause was not the list append an earlier commit replaced but `live`, which filters
the whole waiter list with a per-element `token.isSet` read. That walk is what makes a cancelled waiter
discoverable — a parked waiter holds no `Hooks` registration to retire, so it is found only when the primitive
next touches its list — and it sat on the park path **twice per parked operation**: `acquireStep` walked in the
readiness check and again in the parked branch, and `Channel.prune` walks both the sender and the receiver list,
so the channel's park paid four walks. Pruning is garbage collection over list *length* and not a correctness
requirement: a cancelled waiter left in place is stamped by `ctx.resume`, skipped by `Item.fire`, and consumes
no permit, no slot and no message. So the parked branch no longer re-walks a list its own readiness check has
just cleaned, and the walk that remains runs only when the list has grown past twice its length at the previous
walk (`sweep`), which charges a walk of length L to at least L/2 registrations made since and makes
registration O(1) amortized — parking n waiters is O(n).

The `waiterbench|` rows price both sides of that. The per-waiter cost of parking was **25 016 ns at n=256 rising
to 285 915 ns at n=4096**, doubling with each doubling of n — the quadratic's signature — and is now **flat at
647/448/673/397/1776** ns across the same sizes, 39× to 354× lower. What remains after subtracting the row's own
spawn-only control shows no trend with n; the absolute per-waiter figure tracks the control at every size (at
n=4096, 42 469 ns against 41 887), so the only rise left in the row is the harness's own `spawn` path. The
decomposition above does not price this path, since the served row never parks; the `waiterbench|` rows on the
same line do.

Both sides of that row are a trade, and the trade is what the ratio prices. `Std.Sync.Channel`'s `send` is a
blocking wait: `Channel.Sync.send` is `IO.wait (← Channel.send ch v)`, and the bounded send path underneath
parks the sender on a bare `IO.Promise` — it creates one, enqueues it as a producer and `BaseIO.bindTask`s its
`result?` (`Std/Sync/Channel.lean`) — so the stock channel's per-operation cheapness is bought by occupying a
pool worker for the whole wait, and Lean's pool grows around that (a `Task.get` from a pooled task raises the
pool cap by one, the mechanism `docs/lean-scheduler.md` records). Ours parks the *computation* and leaves the
carrier free, and the CPS closure chain and the mutex transaction this row prices are exactly what buys that. So we are **1.3–2.3× slower per
message because we do not block the carrier** — the same trade seen from the other side in §4.1, where a
blocking call that does not take the pool stops everything — and the row reads as the price of that choice
rather than a plain deficit.

### 4.9 The inject's depth cliff, removed

A loop that spawned 50 000 timer jobs without yielding did not finish in 60 s, reported from a downstream project.
Measured on `8de3ff6` against `8de3ff6` plus the change that replaces the inject's store and `timerPending`
(`Data/Deque.lean`, `Runtime/Io.lean`); 2026-10-31, macOS, 8 cores, elan `v4.35.0`, load average 3.4–4.9. Command:
an out-of-tree probe, three interleaved rounds per row, killed at 60 s, on one carrier through `runCarriersWait`
unless stated. `Task` is `withTimeout 30 s (sleep 1 s)`, spawned by `spawnShared`; `VM` is two 500 ms `VM.sleep`s.

| Jobs | Shape | Before: spawn / total | After: spawn / total |
|---|---|---|---|
| 10 000 | `Task` | 473–494 ms / 2.76–2.87 s | 3.8–4.1 ms / 1.04 s |
| 20 000 | `Task` | 1.59–1.61 s / 13.9–14.1 s | 7.7–8.2 ms / 1.08–1.09 s |
| 50 000 | `Task` | killed, 3 of 3 | 19 ms / 1.19 s |
| 50 000 | `Task`, `Runtime.run` | killed, 3 of 3 | 14 ms / 1.15–1.17 s |
| 50 000 | `VM` | 9.8 s / 53.9–54.7 s | 15–16 ms / 1.11–1.14 s |

**Three causes, separated by ablation** (one round each at 50 000, `Task` shape, on `8de3ff6`):

- **A shared array is copied by every write.** With the placeholder idiom on a bare mutex over 20 000 slots, the
  array's address changed on 2000 of 2000 writes once another thread had reached the cell, and 0 of 2000 before.
  This is the mechanism §The libuv server path records for `lean_st_ref_put`/`swap`, and it is what `Deque` and
  §4.3's "amortised" did not account for. At a depth of 40 000 a push read 155 µs and a pop 207 µs.
- **`timerPending` is the same defect in a global.** Arming read 14 µs each at 5 000 pending and 234 µs at 80 000.
  A single-carrier driver only drains it when its queues are empty. Replacing the inject alone left `Runtime.run`
  at 33–35 s, and with both it read 1.15–1.2 s; `runCarriersWait` was already fixed by the inject alone, because its
  pump drains the hand-off.
- **`popInject` held `st` across the pop**, so pops copied on an unshared cell too (60 µs at 40 000, 52 ns with `st`
  released). Fixing this alone left every shape killed at 60 s. It is moot with the two-list store.

**The price:** the reversal is paid in one pop, under the lock. On the new store the worst single pop read 2.2 ms
at a depth of 100 000 and 23 ms at 1 000 000, and the mean 133–138 ns. The old store's pop read a mean of 172 µs at
20 000.

**The ring is not fixed by this.** At `cap = 256` and depth 0, a push and a take each read about 720 ns on a shared
cell (7.2 µs at `cap = 4096`), and about 300 ns unshared (3 µs). Releasing `p` before the write took the unshared
arm to 48–89 ns independent of `cap`, one run each, and left the shared arm unchanged, so it was not kept: a running
pool's cell is shared. How much of a request this is was not measured.

**Decision:** keep. `tests/queue-scaling.sh` holds it: on the unfixed code it read `inject` 15.4× and `timers` 20.9×
at 16× the depth, with its control at 18.3×; on the fixed code 0.99× and 1.07×, with the control at 14.2×.

### The libuv server path (W16): the socket layer without the promise bridge

`c/netuv.c` and `LeanIn/Runtime/Io.lean` are a server-side socket layer on our own libuv loop. The five
operations `Http.serveConn` and the accept loops use — `Listener.bind`/`sockName`/`accept`,
`Conn.recv`/`send`/`sendAll`/`shutdown` — keep their names, types and semantics, `Http.lean` and the accept loops
are unchanged, and the handler still runs on one of our carriers (SC19's `carrierThreads = 1` holds). What
changes is where a completion comes from: the shim's loop runs on a dedicated stock Lean task, and it resolves
the runtime's own `Join` cell through `Runtime.sharedPush`, so it no longer matters that the lease arrives
through a promise.

**Where it lands, connection-per-request, the same client and mode as §2's baseline** (`load.mjs`, `close`,
5-second runs, `server static`):

| connections | `Std.Async` path | libuv path |
|---|---|---|
| 1 | 2 864 req/s | **4 024** (p50 112 µs) |
| 8 | 5 096 | **7 585** |
| 32 | 3 722 | **6 103** |

The `Std.Async` column is from the run notes rather than re-measured on this machine, so the multipliers (1.40×,
1.49×, 1.64×) are indicative. The error column is not: 61–80% before these fixes, **0** at every level after.

**The four-way, keep-alive, echo handler, every server on this box inside one run** (`threeway.sh` in the run
notes), with the load caveat stated below:

| server | C=1 | C=8 | C=32 | CPU per request, C=1 |
|---|---|---|---|---|
| Node 22 | 31 833 | 70 175 | 73 396 | 24 µs |
| leanin, `Io.lean` | **8 273** (p50 79 µs) | **10 259** | **6 712** | 118 µs |
| leanin, `e2b2988` | 5 103 | 5 560 | 4 157 | 199 µs |
| shipped `Std.Http.Server` | 666 | 1 548 | 1 382 | not read — the pid sampled was the wrapper |

Against the path it replaces: 1.62× / 1.85× / 1.62×, on **1.7× less CPU per request** (118 against 199 µs).
Against the shipped Lean server: 12.4× / 6.6× / 4.9×, where the path we replaced *lost* at C=32. Against Node it
is 3.8× / 6.8× / 10.9× behind — and the gap that matters, CPU per request, has gone from ~120× (this document's
earlier reading of 2 072–2 148 µs against 17 µs) to **~5×**. **The load average was 4.8–6.0 through that run and
Node's own row sits below its recorded 41 195 / 95 800, so the absolute figures are depressed and the ratios are
what to read; a settled re-run is owed for the record.**

**That re-run, at the four-way's own levels** — `bench/threeway.sh`, which is this driver committed rather than
kept in run notes, so the rows below are re-runnable from the tree
(`nix develop -c bash bench/threeway.sh 1 8 32`). Load average **2.59**, echo handler, one invocation, 5 s per
point:

| server | C=1 | C=8 | C=32 |
|---|---|---|---|
| Node 22 | 45 380 (p50 20 µs) | 139 857 | 101 042 |
| leanin (this commit) | 29 932 (p50 29 µs) | 42 241 | 37 705 |
| shipped `Std.Http.Server` | 2 166 (p50 400 µs) | 3 363 | 2 687 |

The shape is the contended run's, less the depression the paragraph above names. Against the shipped server ours
reads **13.8× / 12.6× / 14.0×**; against Node we are **1.5× / 3.3× / 2.7×** behind at the three levels. That
last direction is neither the parser nor the driver: `Server.lean` runs `workers := 1`, one carrier, so added
connections queue on a single thread while Node's one event loop stays ahead by not paying the handoffs. The
`e2b2988` row above is left as history and not re-read — it is a superseded commit, and re-reading it costs a
build of that commit for a path nothing runs now.

**The compiled `async` driver, four arms** — `nix develop -c bash bench/threeway.sh 1 8 32`, which now
builds `hello` too; one invocation, 5 s per point. Both sides are pinned to distinct P-cores (server core 1,
client core 2; `THREEWAY_SERVER_CPU`/`THREEWAY_CLIENT_CPU` override) and the host's energy-performance
preference is `performance`. Those two conditions are not optional: this host is an Intel Ultra 7 268V with
P-cores 0–3 and E-cores 4–7, and an unpinned client lands on either, which moved the rows below by up to 50 %
when it was not controlled.

| server | C=1 | C=8 | C=32 |
|---|---|---|---|
| Node 22 | 70 018 (p50 12 µs) | 146 999 (44 µs) | 150 085 (200 µs) |
| compiled driver (`server`) | **77 891 (12 µs)** | 114 058 (63 µs) | 104 369 (283 µs) |
| compiled, no protocol work (`hello keep`) | 77 150 (11 µs) | 197 070 (35 µs) | 168 592 (165 µs) |
| shipped `Std.Http.Server` | 5 163 | 5 773 | 7 577 |

Against Node: **1.11× at C=1**, 0.78× at C=8, 0.70× at C=32. Per-request CPU, measured from `/proc` deltas over
a pinned run (`server` on core 1, client on core 2, C=8): driver 8.2 µs, Node 6.7 µs, no-parse control 4.8 µs.
So the serving path, the shim and raw delivery cost less than Node's whole server, and the deficit is the
difference between 8.2 and 6.7 — the parse, pump, framing and handler that the no-parse control does not pay,
of which `h1bench` attributes 0.41 µs to parsing. The follow-up work named by that decomposition is the pump,
not the I/O path. The instrument's ±30 % spread (§4.7) applies; these are single-run rows per point.

**The swept read deadline.** The per-read stall bound used to arm a timer per read: a mutex, a
cancel token, closures, a `timerPending` push and a wheel insert, plus a later inert fire. It is now a slot the
read writes and the driver expires on its own poll timeout — no scheduling on the request path. Same-session
A/B, server core 1 / client core 2, three runs each: **8.39–8.59 → 7.28–7.66 µs CPU/request**, 112.4–115.4 k →
**120.4–132.7 k rps**, p50 63–65 → **55–58 µs**. The pinned threeway then read **116 191** against Node's
**100 431** at C=8 (1.16×) and 106 673 against 103 433 at C=32 (1.03×). The harness-clock path is unchanged
(`Clock.swept`), so SC20-O3/SC24 keep their exact instants.

**Keep-armed reads.** The shim used to arm and disarm a read per submission (`uv_read_start` /
`uv_read_stop`, an `epoll_ctl` pair per request). It now arms once, buffers arrivals up to 256 KiB, delivers one
event per pending read and re-arms after a take. Interleaved sign test, five pairs per shape: depth-1 medians
126.3 k → **133.8 k (+5.9 %)**, depth 16 471.1 k → 482.8 k (+2.5 %), 5/5 wins in both; repeated on the ported
build at higher host load, 125.0 k → 130.9 k, 5/5. The same server at depth 16 reads ~483 k against Node's
~106 k in the pipelined shape.

**The ratio needs pairing, not a larger sample.** Two defects made the single-shot rows unusable as a claim.
First, absolute rows drift with the host's state by up to 50 %, and both arms drift together; pairing the arms
inside one round — both servers up, one arm after the other, order alternating, the ratio computed *within* the
round and only then medianed — cancels that drift where averaging rows cannot. Second, a server left running
across levels carries heap and connection state into the next: over one long invocation Node's C=32 rows fell
about 30 % while ours held, which reading rows alone would have reported as a win for us. `bench/paired.sh`
does both, restarting both servers fresh at each level. Nine rounds per level, five seconds per arm, host load
2.3–4.5:

| level | leanin / Node, median of round ratios | IQR | medians, node / leanin |
|---|---|---|---|
| C=1 | **0.94** (pre-fix runs: 0.912–0.952; post-fix: 0.936–0.937) | 0.926–0.956 | 68 074 / 64 826 |
| C=8 | **1.002** | 0.958–1.006 | 124 501 / 123 819 |
| C=32 | **1.237** | 1.179–1.274 | 84 565 / 106 753 |

**So the C=1 deficit is real but smaller than a single run suggests**: ~6 % across paired runs (0.91–0.95), and it
is the protocol layer rather than the I/O path: in the same session the compiled driver with no protocol work
(`hello keep`) read 79 692 against Node's 74 427 at C=1, so the runtime, shim and raw delivery are already faster
than Node, and the ~3 µs gap is parse, pump, framing and response encoding. **The C=8 "0.84×" in earlier
single-run rows was drift, not a deficit** — paired, the two are level (1.002, IQR straddling 1.0). At C=32 we
are ahead by ~24 %; Node's absolute there settles near 85 k in this harness after warm-up, which is why the
ratio, not the row, is the claim. The four-arm three-way remains the instrument for the shipped-server
multiplier (medians of three invocations, load 3.31→6.76: Node 74 427 / 89 950 / 92 055, driver 69 096 / 122 546
/ 109 623, `hello keep` 79 692 / 181 354 / 176 237, shipped server 4 306 / 4 456 / 6 709 — 12–24× our favour).
Per-request CPU still grows with connections (7.0 → 8.3 µs from C=8 to C=32), which is the remaining gap and
the subject of the scaling note.

**Part of that C=1 deficit was ours, and it is now mostly recovered.** The pre-change build (`1f1afdf^`, before
the deadline sweep) paired two-armed against the post-change one read **1.097 at C=1 — 9/9 rounds** (IQR
1.091–1.104), so the changes cost ~9 % at one connection; attribution by the same method put ~7.4 % on the sweep
and ~2 % on keep-armed. Four ablations of the deadline commit — the per-iteration stall scans, the per-read stall
bookkeeping, the `if cfg.clock.swept` branch, and the `rawLive` probe — each still measured ~1.09–1.10, so the
cost was not in any one of those pieces. A poll trace found it instead: the deadline's slot exists only for
reads, so while a response **write** was outstanding there was no deadline at all, `nextDue` was `none`, and the
driver polled at **1 ms** — one extra `epoll_wait` per request (241 045 polls for 239 660 requests, where the
pre-change driver had none). Blocking on an event instead of a 1 ms timeout (`| none => if nothing then 0 else
1000`) measured **+6.2 % at C=1 (9/9, IQR 1.059–1.072)** and is neutral at C=8 (0.996) and C=32 (1.000). With it
the paired C=1 ratio against Node reads **0.936–0.937** across two runs (Node 77.6–78.1 k, ours 72.9–73.1 k),
against 0.945 before the change and ~1.04 for the pre-change build; one traced iteration per request remains
(2.99 polls/request against the pre-change 2.1) and is not yet removed — removing that iteration is the next
step toward C=1 parity. At C=8 and C=32 the same changes are what the wins above measure: ~15.6 % and ~10 %
ahead of the pre-change build paired (1/0.865 and 1/0.909, 9/9).

**The direct-write fast path is inert on the serving path (measured, and its earlier claim withdrawn).** The
shim's `uv_try_write` branch is gated on `g_loop_running`, and counters added to the shim show, over 200 write
submissions from the server, **`gate_loop=200`, `attempts=0`, `ok=0`** — the flag is false throughout dispatch,
so the branch never runs and its recorded "+2.6 % at C=1" was noise between builds. The branch remains in the
shim because it is upstream code and its reachability in the pump-driven entry (where `g_loop_running` is set
around non-blocking iterations) is unverified; the served path does not exercise it. Activating it needs the
ownership contract and completion-first progress the review note describes, not a widened flag: a submission
must be attributable to the loop's owner across dispatch, and a recorded completion must be delivered before any
blocking poll.

**The event bridge carries `UInt32` fields (candidate 1 of the review note).** `np_uv_events` built an
`Array UInt64`; on 64-bit `lean_box_uint64` allocates a constructor per field, so one request's read and write
completions cost six box objects. Both sides now carry `Array UInt32` — `lean_box_uint32` is an immediate — with
the sign of a libuv status decoded explicitly from two's complement (`signed`) rather than from a 64-bit
encoding. Paired, nine rounds per level: **1.028 at C=1 (IQR 1.010–1.032), 1.005 at C=8, 1.009 at C=32**.
SC19/20/23/24/27 and BT1–3 pass, covering EOF and negative-status paths. Measured on `5b74698`; the change
landed as `c24f381`.

**Candidate 2 was then tested both ways, and both were rejected.** *Owner-gated direct writes*: the write path
was re-gated on an explicit loop-owner claim (taken in `takeover`, released when the driver finishes) instead of
the polling flag, with `c->writes` counting queued writes too so ordering holds. Counters confirm the branch now
runs — `calls=200, attempts=200, ok=200` — and it measures **0.972 at C=1, 1.011 at C=8, 0.985 at C=32**: making
the fast path live makes C=1 and C=32 worse. *Completion-first progress*: returning from the poll when a
submission has already recorded events measures **0.981 / 0.976 / 0.950** and is additionally not
semantics-preserving as written, because it returns before arming the wheel timer the swept deadline relies on.
Neither variant is in the tree. The counters and the owner contract remain the useful artefacts: they settle that
the old branch was inert (`gate_loop=200, attempts=0`) and that activating it is not a win on this driver.

**Clean per-request attribution, and candidate 3.** Differencing profiles at 300 and 1000 requests gives
**58 807 Ir/request** (700-request delta, startup cancels). The top terms: `lean_dec_ref_cold` 8 668 (14.7 %),
`mi_free` 4 535 (7.7 %), **`lean_mark_mt` 4 282 (7.3 %)**, `lean_alloc_small_object_core` 2 390 (4.1 %),
`Std.Mutex.atomically` on a cancellation token 2 095 (3.6 %), `lean_apply_2` 1 517, pthread lock/unlock 2 267,
string building (`utf8_set` + `append` + `shouldKeepAlive`) 2 954, `driveOnce` 1 098, `findLF` 1 018,
`copy_expand_array` 1 008. The review note's candidate 3 has a real 7.3 % ceiling, and the ablation of the whole
stall machinery measures 2 941 Ir/request (5.0 %).

**The stall slot now carries data, not a continuation.** `StallSlot` holds only its deadline, and the sweep
delivers the timeout as `.ok .timedOut` through the raw registration instead of calling a stored `fire` closure.
`recvStallRaw` registers directly (the `recvRaw` wrapper maps any non-`read` result to an error, which would have
turned a timeout into a mismatch error). This removes the per-read closure allocation and its publication into
the global stall table — 1 083 Ir/request (1.8 %). Paired: **1.016 at C=1, 1.025 at C=8, 1.012 at C=32**. SC24
still reports the stall at the exact instant and every other scenario passes. The remaining publication is the
raw registry's resume closure, which is where the rest of the 7.3 % marking term lives.

**The raw registry's publication cost, measured, and why it is not simply removed.** Replacing the registry's
`Std.Mutex` with an `IO.Ref` (same `HashMap`, no lock) saves **1 810 Ir/request (3.1 %)**, which locates the
marking cost at the mutex publication rather than at the hash operation. It is not shippable as written:
`recvRaw`/`sendRaw` are public, and an unsynchronized `IO.Ref` is a data race the moment a raw operation is
submitted off the driver thread — the cross-thread-state rule this repository states elsewhere. The shape proposed as the safe substitute — a per-connection trampoline capturing a cell and registered once —
was then tested and **withdrawn**: publishing a cell into a persistent global reference, and then writing fresh
16 k-`UInt32` state into it, makes the identical update cost **22 984 ns/iter against 277 ns/iter** for the same
cell never published (same `modifyGet` + `set!`, 2000 iterations). The runtime sources confirm why
(v4.35.0-rc3): `lean_mark_mt` traverses closure environments and ref contents, and `lean_st_ref_put`/`swap` mark
the stored value whenever `ref_maybe_mt(ref)` — when the reference is itself multi-threaded *or persistent*.
Indirection through an ordinary cell is not an ownership boundary, so the trampoline cannot take the marking
term; the driver-private context (variants C/D of the ownership handoff) is the remaining design.

**Cumulative effect of the handoff's changes** — current server code (`f2dbf02`) against the pre-handoff
revision (`5b74698`), paired, nine rounds: **1.009 at C=1, 1.021 at C=8, 1.024 at C=32** (measured on `729d9e2`;
the C=1 interval straddles 1.0, so no gain is claimed there).


**What the remaining gap is made of (C=1, pinned, `/proc` CPU per request).** The compiled driver costs
**12.07 µs** per request against Node's **8.92 µs**, but the same runtime and shim with **no protocol at all**
(`hello keep`) cost **9.47 µs** — already more than Node's whole request. The HTTP layer is therefore only
**2.6 µs** of the 12.07, and no amount of protocol work can close the C=1 gap on its own; the per-operation
runtime path is the floor to attack. Two bounds on the protocol side: `encodeResponseHead` measures **235 ns**
per call in isolation (2 % of a request, so rebuilding it cannot pay), and the profile's remaining protocol spend
is refcount/alloc/free (~6.7 k Ir) — worth a few percent, not the 10 % needed. The runtime path's cost is the raw
completion: per read and per write, a closure plus a `Std.Mutex (HashMap (conn, op) closure)` insert/erase and the
executor/loop handoff. Replacing that with fixed per-connection slots holding a data state (the "data, not
closures" design) is the change that can reach the ~1.2 µs a 10 % cut requires; an earlier Lean-side slot attempt
collapsed to ~9 k rps — one request per millisecond per connection — which points at the driver's idle/liveness
test around the slots rather than the storage shape, so it is a retry with the write-wait path now understood,
not a repeat of a dead end.

**Fixed-slot raw registry, retried and rejected.** With the liveness count and the slots in one structure under
one lock (so they cannot drift), and the 16 k-entry collapse explained as array copying, the registry was sized
to 256 entries — enough for 64 connections, larger than the benchmark uses, and small enough that copying is
free. It measured **0.968 at C=1 and 0.871 at C=32** against the HashMap build: fixed Lean slots under
`Std.Mutex` are slower than the hash insert they replace even when the array is small, so the shape is rejected
on its own merits rather than on a bug. The registry is not where the floor is.

**Thread topology: the request path is single-threaded.** The runtime shows three OS threads under the
benchmark: the initial thread (parked in `futex`), the driver thread, and one idle thread parked in `ep_poll`
whose creator is not yet identified. The **driver thread is the loop and the handler** — the non-quiet server
prints the handler's thread id and it is the same thread that drives `blockOnIo` and burns the CPU (154 of 156
ticks in a two-second window) — so the request path is single-threaded, as `blockOnIo`'s design states. The pump
started by `startListener` (needed only in the window between `bind` and the driver's `takeover`) is asked to
quit and does: traced with the synchronized flags, it enters and exits, and its id is absent afterwards. It is not
the idle thread. The executor worker is excluded too: `workers := 0` still leaves three threads while the server
serves correctly. So the extra threads are runtime scaffolding, one still unnamed; a literally single-threaded
process would need Lean's own initial thread and that one removed, which is outside this runtime. An experiment
giving the process a second core read 1.037 at C=1, but a one-core control read 0.965 and only one thread does
work, so that figure was placement and host noise and is withdrawn.

That investigation did surface a real violation: `pumpQuitRef` and `driverActiveRef` were plain `IO.Ref Bool`s
written by the driver's thread and read by the pump thread and carriers — the cross-thread-state rule this
repository states elsewhere (`runWith`: "a plain `IO.Ref` would be a violation"). They are now `Std.Mutex Bool`
flags with locked get/set, so a quit request cannot be lost. Paired against the commit before it, nine rounds per level, it measures
**0.991 at C=1** (IQR 0.984–1.027), **0.997 at C=8** (0.979–1.010) and **1.006 at C=32** (1.001–1.013) — neutral,
as expected for flags read by `startListener`/`takeover`/`liveSchedule` rather than per request. SC19/20/23/24/27
and BT1–3 pass.

**Sustained load, the realistic shape.** One server at a time, pinned, driven back to back for 150 s at C=32 and
120 s at C=1 (5 s samples, no gaps), to test whether leaving the server up favours ours:

| level | arm | first window | last window | min–max |
|---|---|---|---|---|
| C=32 | Node | 147 587 | 127 491 | 115 659–149 940 |
| C=32 | leanin | 119 660 | 117 047 | 102 331–130 541 |
| C=1 | Node | 70 480 | 66 744 | 48 782–75 269 |
| C=1 | leanin | 60 471 | 60 538 | 58 682–65 107 |

Node degrades under sustained load (148→127 k, −14 %) and has hiccups (one window at 48.8 k), but ours degrades
too (130→117 k, −11 %), so the ordering is unchanged: Node ahead at C=1 and C=32, level at C=8. The 84 k C=32
reading behind the withdrawn 1.24× row was an outlier in our own environment, not Node's steady state; the
sustained series above is what the "left running" case actually looks like.

**The C=32 "win" was Node's slow tail, and the distribution settles it.** Six alternating runs per level with
both servers pinned and each kept up for the level: at C=8 Node read 103 735–146 120 (median 126 877) and ours
101 003–135 711 (median 128 456); at C=32 Node read 113 494–141 220 (median 125 474) and ours 103 508–121 607
(median 116 108). At C=1 the paired runs read Node 68–78 k and ours 62–73 k. So Node's spread is ~40 % at the
high levels while ours is ~10 %; on medians we are level at C=8, ~4 % behind at C=1 and ~8 % behind at C=32, and
at Node's best it is ahead at every level. The paired ratios are still the right instrument for a *comparison
within one invocation*, but a ratio against a server whose own spread is 40 % cannot support a standing claim of
the form "1.24× at C=32"; the earlier row that reported one is withdrawn, and the absolute distributions are the
record.

Two further attempts were measured and discarded. Suppressing the async wake for loop-thread submissions removed
the empty poll but collapsed the server to ~1.5 k req/s: the wake is load-bearing on that path. Caching the stall
table's earliest deadline (one lock and no per-iteration traversal) measured 0.990 against the current build — the
2.3 % that removing the scan calls had shown did not come from the traversal. Neither is in the tree.

**Load shapes** — measured on `41943fa` with `bench/screen.sh` (`bench/screen.sh`: d1 = keep-alive depth 1, p16 = 16 requests in flight per connection,
churn = one connection per request), one server per arm, 5 s per point, load 2.5 rising to 6.6 through the run.
Requests per second:

| shape | arm | C=1 | C=8 | C=32 |
|---|---|---|---|---|
| d1 | Node | 70 593 | 146 038 | 147 049 |
| d1 | leanin | 66 040 | 150 736 | 132 916 |
| d1 | shipped | 5 463 | 5 851 | 7 733 |
| p16 | Node | 173 792 | 181 052 | 181 153 |
| p16 | leanin | **419 596** | **521 336** | **508 627** |
| p16 | shipped | 7 636 | 11 572 | 12 649 |
| churn | Node | 29 988 | 48 526 | 51 064 |
| churn | leanin | 15 430 | 43 486 | 50 762 |
| churn | shipped | 2 808 | 2 044 | 1 546 |

Pipelining is where the runtime pulls ahead: **2.4×, 2.9× and 2.8× Node** at the three levels, with p50 35 vs
82 µs, 232 vs 639 µs and 972 vs 2583 µs. At depth 1 the two are within 10 % either way. Connection churn is the
shape we lose: at C=1 we serve 15 430 against Node's 29 988 (p50 29 µs, p99 879 µs), recovering to parity by
C=32; the close path drains the peer's end of stream before closing rather than resetting, which is the
behaviour that removed the reset storm, and its cost shows here. Against the shipped server we are 5–12× ahead
in d1, 22–40× in p16, and 5–33× in churn.

**The raw registry moves to C (`e55b7db`).** The marking term was attacked at the ownership boundary rather
than through indirection: the shim now holds one **owned Lean closure pointer** per `(connection, op)` in a
C array behind the shim's own mutex, instead of a `Std.Mutex` holding a Lean `HashMap`. Storing a closure in a
Lean reference — global or reached through one — marks it and its captures multi-threaded, which is what the
publication control showed (22 984 vs 277 ns/iter), and then every exclusive update copies. A C pointer is not
visible to that classification, the shim still never calls Lean, and the public raw operations keep a real lock;
taking an entry transfers ownership back to Lean, and a withdrawn entry is dropped.

Measured against `133aff1`: **47 970 Ir/request against 58 807 (−18.4 %)**, and paired, nine rounds per level,
**1.121 at C=1 (IQR 1.103–1.127), 1.183 at C=8 (1.175–1.202), 1.400 at C=32 (1.354–1.416)**. SC19/20/23/24/27
and BT1–3 pass, including SC24's exact stall instant; a 30 s mixed stress run at C=8 (keep-alive 177 690 rps,
pipelined 484 298 rps, churn 42 096 rps) reports zero errors and the server stays healthy.

The load-shape screen on `e55b7db` (one invocation; load rose from ~2.6 to 7.4 during it, after Node's rows):

| shape | arm | C=1 | C=8 | C=32 |
|---|---|---|---|---|
| d1 | Node | 70 729 | 124 145 | 112 915 |
| d1 | leanin | 70 250 | **144 518** | **162 714** |
| d1 | shipped | 5 592 | 5 499 | 7 321 |
| p16 | Node | 169 492 | 148 022 | 141 954 |
| p16 | leanin | **352 966** | **432 545** | **456 357** |
| p16 | shipped | 7 495 | 11 782 | 11 622 |
| churn | Node | 29 054 | 35 442 | 39 942 |
| churn | leanin | 15 310 | 35 961 | 42 521 |
| churn | shipped | 2 611 | 2 212 | 1 500 |

Depth-1 is at parity at C=1, **1.16× at C=8 and 1.44× at C=32**; pipelining is **2.1–3.2×**; churn is still
0.53× at C=1 and 1.02–1.06× by C=8/C=32. The C=32 depth-1 figure is the one to re-check on a settled box: Node's
rows were taken before the load rose, so the ordering is conservative rather than flattering.

**Second screen, on the hardened build (`554e3b0`).** Same command and method; load rose from ~2.5 to 8.1
during the run and Node's rows were taken first, into the lighter load. Requests per second:

| shape | arm | C=1 | C=8 | C=32 |
|---|---|---|---|---|
| d1 | Node | 64 100 | 140 011 | 144 473 |
| d1 | leanin | 62 568 | 147 791 | 126 481 |
| d1 | shipped | 5 323 | 5 584 | 7 626 |
| p16 | Node | 164 090 | 168 179 | 177 930 |
| p16 | leanin | 424 573 | 512 451 | 411 417 |
| p16 | shipped | 7 472 | 11 436 | 12 462 |
| churn | Node | 26 067 | 46 106 | 48 686 |
| churn | leanin | 16 128 | 42 115 | 39 992 |
| churn | shipped | 2 815 | 1 923 | 1 438 |

Against the earlier `e55b7db` run this is 0.98 / 1.06 / 0.88 at depth 1, 2.59 / 3.05 / 2.31 pipelined and
0.62 / 0.91 / 0.82 under churn: the pipelined lead reproduces, depth-1 C=32 and churn move with the load, and the
honest reading is that the screen is an illustration, not a ratio claim — `bench/paired.sh` remains the instrument
for that. Depth-1 C=32 is the figure most sensitive to a busy box and is the one to re-check settled.

**The close path is where the resets were, and it was worth more than everything else here together.** The first
version closed the handle from the shutdown callback. Closing a socket whose receive buffer still holds unread
data makes the kernel send RST instead of a clean FIN, and in `close` mode the receive side is nearly always
dirty: reading stops at the header terminator, so the peer's FIN is never read and neither is a pipelined
request. That made the client's error column a report of *our* resets rather than the client's own reconnect
race, and each reset was a connection the server accepted, read and closed for nothing — which is why
`completed`/s under-credited the server by roughly five-fold at C=8. `on_shutdown` no longer closes: a connection
whose write side has gone is drained to the peer's end of stream first, and only then closed. Errors went to zero
and C=1 close-mode went 1 160 → 4 024 req/s.

**Still open on this path.** A full 16 384-slot event ring is treated in `c/netuv.c` as an impossible internal
state, and `Io.lean` throws on it: the loop thread dies, every parked operation hangs with it, `Io.stop` re-raises
during shutdown and the process ends inside its own exit path, with the message reaching no log. It is reachable
from load. The sibling condition is worse if it is reached — a refused submission (`MAX_SUBMIT`, 8 192) returns 0,
and a caller that parks anyway hangs a connection silently, with no error anywhere. Both are correctness items
before they are performance items. And C=32's p50 (2.35 ms against C=1's 79 µs) says the per-operation cost is
still the ceiling at concurrency: the number of shim operations a request costs has not been counted, and the
loop thread does not yet double as a carrier.

**What the instruments did establish, on a server that survived:**

- **It is not one thread and it is not spinning.** Per-thread CPU over a window of a C=1 run and a C=8 run
  (`/proc/<pid>/task/*/stat`): the carrier and the loop thread each consume roughly half a core at C=1 and
  saturate together at C=8-plus. Over the same window the carrier reads 5 280 ms user against 370 ms system, the
  loop thread 3 960 against 980, and the context switches are 84 351 voluntary against 2 021 nonvoluntary (carrier)
  and 77 609 against 1 770 (loop thread). So the cost is **Lean work on both sides of a handoff**, not syscall
  traffic and not a contended lock — a hypothesis those counters refuted rather than supported. The per-operation
  share is ~32 µs of user CPU on the loop thread and ~364 µs per completed request on the carrier, and what that
  364 µs is *made of* is not yet localised.

- **`completed`/s under-credits the server, and the gap grows with connections.** The client's error share —
  each error a connection the server also accepted, read and closed — reads 61% at C=1 and **80% at C=8**. So at
  eight connections the server does roughly five connections' worth of work per request the client counts. In the
  one run where both instruments were read, the server served 6 633 while the client completed 5 295 (different
  runs, so not a clean pair). The calibration has since run: against the same client in keep-alive mode,
  `e2b2988`'s path shows **no** such inflation (0 errors at every level) and the path above still beats it at every
  level — so the multiplier was ours, and the close-path fix is what removed it.

- **Where the CPU actually is, from a profile rather than from arithmetic.** `callgrind` over ~1 100 requests at
  one connection (keep-alive, echo handler, `server static quiet`) records **300 M instructions, about 272 000 per
  request**, and its self-cost table is a memory-management table: `lean_dec_ref_cold` 16.1%, `lean_mark_mt` (the
  GC mark phase) 8.2%, `mi_free` 8.1%, `lean_alloc_small_object_core` 3.8%, `mi_theap_malloc_zero` 2.8%,
  `lean_alloc_object` 1.6%, `lean_free_object` 1.2% — **allocation, refcounting and GC together above 42%** — with
  closure application (`lean_apply_1/2/3/4`) about 12%, `Std.Mutex` and `pthread_mutex_lock`/`unlock` under 3%,
  the H1 header scan (`Parsec.ByteArray.scanWhileUpTo`) 0.9%, and `c/netuv.c` absent from the top 22 entirely.

  The inclusive view says where those objects come from: `Join.deliver` 46.9%, `Item.ofDeferred` 47.4%,
  `Item.fire`/`fireAt` 54.7%, `Http.drive`'s loops ~35%, `EAsync.ofAsync` 28.8%. So roughly half the program is
  the **completion-delivery path**, allocating closures, waiter records and items per completion and paying
  refcount and GC on them — not the socket layer, not the locks, and not the HTTP machine.
  `lean_copy_expand_array` at 2.1% is the per-iteration event array: real, small, and worth doing, but not the
  story.

  What this rules out is worth as much as what it names. The remaining cost is **not** in the shim, **not** lock
  contention (which the context-switch counters had already refused), and **not** the per-read deadline's timer
  arming. The lever is fewer and cheaper objects on the delivery path.

- **The gap at one connection is orchestration, not work.** `voluntary_ctxt_switches` summed over a server's
  threads and divided by the client's completed requests — keep-alive, one connection, echo handler, `quiet` —
  reads **7.98** for this path against **0.93** for Node, in the same shape: 4 895 against 18 843 req/s, p50 162
  against 39 µs. At ~10–15 µs per handoff that is essentially the whole latency difference.

  The decomposition is exact, from the gated operation counters: a keep-alive request costs two shim operations
  (read and writev), and each costs four switches — the completion wake, the carrier's wake, the carrier's
  submission while the loop is parked, and the loop's wake to apply it. The wake suppression committed in
  `b1afd0b` applies only while the loop is *running*, which is not the case in that steady state, so it removes
  less than it could; the figure above is *with* it, and would read higher without.

  **This is the measurement that instruction counting cannot make, and the reason the two disagree.** `callgrind`
  serialises the two threads, so the same path reads a *favourable* 277 943 instructions per request against
  Node's ~378 000 while being four times slower in wall time — the counts are sound and the conclusion drawn from
  them was wrong. The instrument to reuse is the switch count: a count, therefore load-invariant on a machine that
  never idles, and the only one in this section that prices waiting rather than work.

  Reproduce it with the shell's own `valgrind`: start the server under
  `nix develop -c valgrind --tool=callgrind --callgrind-out-file=/tmp/cg.out ./.lake/build/bin/server <port> static quiet`,
  drive it with `load.mjs` in keep-alive at one connection for a few seconds (callgrind is 20–50× slower, so a
  small load is the point), and read it with `nix develop -c callgrind_annotate --inclusive=yes /tmp/cg.out`.

- **The 41 ms floor was ours, and no scenario could see it.** Before the fix, stage timing put 4–5 µs in
  enqueue→apply and 42 244 µs in apply→completion; the shim asked for the read promptly and the completion
  arrived 41 ms later. `Conn.sendAll` was issuing one `uv_write` per buffer, so a response went out as two
  back-to-back small segments and the peer's delayed-ACK timer held the second, and the accepted connection
  never had `TCP_NODELAY` set. The old `sendAll` wrote them as one operation, which its own docstring states —
  **a documented promise that none of SC1–SC22 asserts**, found by measurement rather than by the contract.
  With both fixed the floor is gone (308 / 127 / 77 / 208 µs for successive responses on one connection) and C=1
  close-mode moved 1 160 → 2 509 req/s.

**Not a comparison.** The spike that motivated this path measured 5 538–10 494 / 14 934–18 664 / 18 025–21 496
req/s, and it is ⚪ here for a reason worth stating: it handled each request *on the loop thread*, so it had no
handoff at all, and it parsed no HTTP. Those figures are a ceiling for a different shape, not a target this one
is failing to reach.

### The read deadline's thread, removed: the timing wheel

`Clock.live`'s `sleep` was `awaitAsync hooks (Std.Async.sleep d)`: every `withTimeout` on a read armed a libuv
timer, a promise and a task on the standard library's own loop, and that loop's thread was a third worker the
switch count could see — 2.02 of the 7.98 voluntary switches a keep-alive request cost — plus the seam itself,
~99 µs to await a resolved promise through it against ~11 µs on our own `resumeShared`. The wheel replaces that
with a `Std.TreeMap Nat (Array WheelTimer)` ordered on the deadline, owned by the loop thread that already
services socket completions: a `sleep` is one `Array.push` onto a mutex hand-off queue, the loop thread drains it
in one pointer swap into its own map, and it wakes for the earliest deadline exactly as it wakes for I/O, through
one `uv_timer_t` armed to that deadline. There is no third thread, and no second worker appears in SC19's
`carrierThreads`.

Same client and mode as the 7.98 row above (`load.mjs`, keep-alive, one connection, echo handler, `quiet`, 5 s):

| | baseline (`Std.Async.sleep`) | the timing wheel |
|---|---|---|
| throughput | 4 895 req/s | **12 767 req/s** |
| p50 | 162 µs | **63 µs** |
| p99 | 535 µs | **229 µs** |
| voluntary switches / request | 7.98 | **4.78** |

🟢 on every row, and the gate holds at 22/22. The 2.6× throughput is mostly the seam, not the switches: taking
the ~99 µs `awaitAsync` bridge off the read's critical path is what moves p50 from 162 µs to 63 µs, and at one
connection the throughput follows the latency. The switch figure is with the losers accumulating — `withTimeout`
leaves each deadline in the wheel (D20), so thousands of 12 s entries accumulated in the measured run — and it is
the ordered map that keeps that cheap: the loop's two per-iteration readings, the earliest deadline for the park
timeout and the timers already due, are O(log n) where a flat list paid O(n) for the same pair, which is what
halved an earlier flat-list attempt's throughput (3 809 req/s) and doubled its p50 (240 µs). The thread that
parked only for timers is gone from the switch attribution entirely.

Reproduce with the switch count from the row above: `./.lake/build/bin/server <port> static quiet`, drive it
with `load.mjs` in keep-alive at one connection for 5 s, and sum `voluntary_ctxt_switches` over
`/proc/<pid>/task/*` divided by `completed`.

### The serving carrier drives the loop: the handoff removed

The W16 path left the loop on its own thread and handed each readiness to a carrier as a scheduled item — the
7.98 voluntary switches a keep-alive request cost, decomposed above as two shim operations at four switches
each. The single-carrier entry now takes the loop over instead: `Runtime.run`'s driver (`blockOnIo`) calls
`Io.driveOnce` on the serving carrier when its queues are empty, so the poll, the completion it records, and the
handler that completion resumes all run on one thread, and there is no handoff left to price. The multi-carrier
and `runVirtual` entries keep a pump thread — their carriers never take the loop over — and `driveOnce`'s
nothing-to-drive test is split between the two shapes: the pump keeps serving while a listener is bound, because
the accept that gives it work is registered by a task it has not yet run; the single-carrier driver, which *has*
taken the loop over, condvar-parks on its own executor's work rather than on a listener another executor bound
(SC20's idle accept is the first case, SC17's bare `Join` wait the second, and one test serving both is what
broke each in turn).

Same client and mode as the 7.98 row (`load.mjs`, keep-alive, echo handler, `quiet`), the merged driver against
its **direct predecessor** `5e608ba` — the timing-wheel path with the loop still on its own thread — interleaved
two reps each so neither sees a systematically fresher box:

| | switches / request | p50 | req/s |
|---|---|---|---|
| C=1, predecessor | 4.82 / 4.81 | 122 / 122 µs | 6 262 / 6 579 |
| C=1, merged | **0.15 / 0.15** | **82 / 78 µs** | **9 181 / 9 326** |
| C=32, predecessor | 1.71 / 1.76 | 1 647 / 1 570 µs | 16 646 / 17 614 |
| C=32, merged | **0.02 / 0.02** | **1 093 / 1 098 µs** | **27 438 / 26 684** |

🟢 on every row. The predecessor's 4.81 reproduces the timing-wheel section's recorded 4.78 to inside this
document's drift band, which is the method check rather than a coincidence: the switch count is the
load-invariant instrument (§4's 7.98 row: it prices waiting, not work), and it says the handoff is **gone** —
32× fewer switches at one connection, ~85× at 32, both **below Node's ~0.93–0.98** in the same shape. p50
follows it (1.5× at both levels) and throughput rises (1.44× / 1.58×). Against Node, from the four-way run of
§4's table re-run at this commit (`threeway.sh`), the remaining gap is p50 **2.1–2.4×** at one connection and
**1.6×** at 32, and CPU per request **2.8×** (108 µs against 38 µs) — narrowed from the ~5× the W16 section
recorded for the predecessor (118 µs against 24 µs). Both leanin figures scale from C=1 to C=32 here (the
predecessor 2.7×, the merged 2.9×); the merged is the higher base at every level.

Two driver bugs were found on the way, and the gate — not the benchmark — is the evidence for them: the shim
reported libuv `EAGAIN` (`nread == 0`) as end-of-stream when only `UV_EOF` is one, which hung keep-alive
teardown (SC20); and one nothing-to-drive test served both the pump and the single-carrier driver, which either
stranded a `runVirtual` accept or loop-parked a bare `Join` wait (SC20 and SC17 respectively). The gate holds at
**22/22** with the fix.

Reproduce: `bash pred-compare.sh` (run notes) interleaves the two servers at each connection level; the
predecessor is a worktree at `5e608ba`, built with `nix develop -c lake build server`. The switch count is
`voluntary_ctxt_switches` summed over `/proc/<pid>/task/*` divided by `completed`, as in the 7.98 row.

### The `Std`-shaped handler layer (D24): what the stock types cost

⚪ **Not an external comparison**: both arms are this runtime, through the same streaming driver; the pair prices
the layer `StdHandler` adds on top of a native `StreamHandler`. Measured on the layer as committed in `9564a64`
(the in-memory rows on the same code before it was rebased onto `main`), with the instruments `dispatchBench`,
`stdBench` and `bench/stdpaired.sh` added alongside this entry, on 2026-10-22, on an
aarch64 Linux container (18 cores, kernel 7.0.14-linuxkit), server pinned to CPU 1 and client to CPU 2, Node
v24.21.0 from `nix shell nixpkgs#nodejs`.

**In memory** (`nix develop -c lake build dispatchBench && ./.lake/build/bin/dispatchBench 200000`, three
invocations, each alternating the arms twice; load average 0.92). `native` parses the head and builds the response
head the writer encodes; `std` adds `headToStock`, the `Request` with its `RemoteAddr`, the stock `Response`, its
conversion back and the cached `Date`; `head` is `std` stopped after `headToStock`. Ranges are over the six
readings per arm:

| request | native | head | std | std − native |
|---|---|---|---|---|
| `load.mjs`'s, two headers | 413–425 ns | 1 626–1 778 ns | 1 750–1 943 ns | ~1.35–1.5 µs |
| browser-shaped, ten headers | 1 915–1 936 ns | 12 880–13 125 ns | 12 987–13 506 ns | ~11 µs |

`headToStock` is nearly all of it, about a microsecond per header. A one-off decomposition of the browser
request (temporary arms, one invocation, not kept) split its ~11 µs as: the header slices to `String`
(`Slice.toString?`, ours) ~1.1 µs; `Std.Http.Header.Name.ofString?` ~3.5 µs; `Header.Value.ofString?` ~4.0 µs;
`RequestTarget.parse?` ~2.1 µs; the map inserts and the rest ~0.4 µs. So ~85–90 % is `Std.Http`'s own
validation and URI parsing — the cost of producing its types at all, which `Std.Http.Server`'s own parser pays
too — and ~10 % is the UTF-8 conversion on our side.

**At the socket, on the target x86_64 host** (`PAIRS=9 DURATION=5 nix develop -c nix shell nixpkgs#nodejs -c
bash bench/stdpaired.sh 1 8 32`, measured on `38f7ccb`: `load.mjs`, keep-alive, depth 1, `/bench`, both arms
started fresh per level and alternated within it; Intel Core Ultra 7 268V, 8 cores, server pinned to CPU 1 and
client to CPU 2, load average 4.06 before and 8.24 after; shared host, so the absolute rates are lower than the
aarch64 container's and only the paired ratios are comparable):

| C | median std/native | IQR | median native | median std |
|---|---|---|---|---|
| 1 | **0.846** | 0.825–0.893 | 15 665 req/s | 13 295 req/s |
| 8 | **0.804** | 0.769–0.831 | 28 171 req/s | 22 697 req/s |
| 32 | **0.779** | 0.735–0.792 | 32 271 req/s | 24 305 req/s |

**On the aarch64 container**, retained as a cross-platform shape rather than the target record
(`PAIRS=9 DURATION=5 …`, measured on `db8be50` with the script's start fix below: same load shape, both arms
started fresh per level and alternated within it; 18 cores, load average 0.25 before, 1.88 after):

| C | median std/native | IQR | median native | median std |
|---|---|---|---|---|
| 1 | **0.886** | 0.880–0.893 | 37 559 req/s | 33 268 req/s |
| 8 | **0.811** | 0.808–0.812 | 105 383 req/s | 85 479 req/s |
| 32 | **0.827** | 0.825–0.828 | 117 890 req/s | 97 333 req/s |

*Withdrawn*, superseded by the rows above: the first run of this table (0.891 / 0.817 / 0.822, IQR within
0.811–0.892) stated both arms were fresh per level, and they were not. `stdpaired.sh` started each server through
a backgrounded shell function, so `kill` reached the subshell and not the server; each later level's servers
failed to bind, and the C=8 and C=32 rounds were served by the C=1 processes. The pairs were still the same two
builds, alternated, which is why the rerun agrees to within 0.006; the script now starts the servers directly
and refuses a port already in use.

At C=32 that is ~1.79 µs more per request (8.48 → 10.27 µs), consistent with the in-memory two-header delta plus
the `Date` and the response conversion. `load.mjs` sends two headers, so a browser's requests would pay more: on
the in-memory figures, roughly ten microseconds more per request.

**Decision.** Keep the layer as an opt-in alongside the native path; **reject** making it the only public
handler shape, which D24 left to this measurement. Both hosts agree on the direction: the layer retains roughly
78–85 % of native throughput at the socket, and the remaining cost is mostly inside `Std.Http`'s constructors.
Cutting it would mean building `Headers` without re-validating what LeanIn's parser has already accepted, which
the public `Std` API does not offer.

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
| `nix develop -c lake exe controls --runtime-blocking` | the blocking pool at the executor boundary (SC12): four 25 ms pool jobs on two threads that are not the carrier, a carrier step falling strictly between the first job's start and its completion, a stock-priority task finishing before the jobs, the outstanding-work peak of four and its final zero with both workers exited, and the timing; plus a `blockctl\|` control counting two on two distinct tids, rejecting the blocking-shaped order and rejecting a record claiming the stock pool was taken |
| `nix develop -c lake exe controls --runtime-shared` | the same counter under each design's required discipline, and what the stock pool loses without its lock |
| `nix develop -c lake exe controls --runtime-sleep` | four 50 ms libuv timers on one carrier — 51 ms, against 200 ms for a serial sleep path |
| `nix develop -c lake exe controls --runtime-net` | 16 concurrent echo connections on one carrier: the connection count, the server's thread count, whether the client shares it, the byte-identical replies, and the pool alongside |
| `nix develop -c lake exe controls --runtime-service --bound=2` | the bounded accept path (SC14): one 5-connection run's wall time, its per-connection share, and the connections/s that implies — the figures §3's service row quotes — plus SC14's `service\|` record and its checker's `servicectl\|` readings |
| `nix develop -c lake exe controls --runtime-time` | 16 × 50 ms sleeps and their event order, two timeout outcomes, the task layer's first-writer law, and the blocking path for the same sleeps |
| `nix develop -c lake exe controls --runtime-drain` | a stop with a connection in flight: whether the connection completes after the stop, whether the pool is empty and whether a leaf registration is outstanding when the run returns, and how long the drain takes |
| `nix develop -c lake exe controls --runtime-cancel` | a disconnect cancelling the work: the counter as it stood in the cancelling step and after the run returns, the work's own registrations before and after, the cancelled handle's outcome, and a second cancellation; plus the `cancelbench\|` row — the cost of the new operation: spawn-and-await against cancelling a parked task, the first-writer flag and resolve, retiring the registration, and the registry's size before and after cancelling 200 parked awaits |
| `nix develop -c lake exe controls --runtime-sync` | the sync primitives' cost (§3.1): lock/unlock uncontended, and contended with the permit held across a yield — the row printing `heldAcrossYield=yes\|no` from the yielding chains' own `tryLock` probe — a release that wakes 16 parked waiters, the semaphore's acquire and release, and a message through the bounded channel beside the same message count through `Std.Sync.Channel` in one run; plus SC13's `sync\|` record and its checker's `syncctl\|` readings, the `waiterbench\|` rows for parking waiters, and the `chanunit\|` decomposition of the served channel operation |
| `nix develop -c lake exe controls --runtime-chan` | the served channel operation decomposed (§4.8): the whole served send/receive, the stock channel beside it in the same run, the bare mutex transaction, the served transaction's `prune`/enqueue split, the `Async` loop skeleton, the parked waiter's `Join`, one step and its `Ctx`, and a native `Task` calibration |
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
