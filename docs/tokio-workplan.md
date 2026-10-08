# A Tokio-shaped workplan

What would have to be built, and what evidence would have to exist, before `leanin` is something you could
write a network service on. Ordered so that each item unblocks the next, with the Tokio-like aspects first.

This extends [`PLAN.md`](../PLAN.md) rather than replacing it: **W4 is its M4** (the blocking pool) and **W8 is
its M5** (multi-carrier and stealing). Everything else is new, and the milestone numbering here is deliberately
separate so the two can be read side by side.

Every deliverable states the artefact and the evidence that it is met. The evidence idiom is the repository's
own: a **scenario** at an external boundary with its controls, a **proof** against the model, or a
**measurement** from `--runtime-bench`, `--runtime-tail`, `--runtime-shared`, `--runtime-ops` or `--spike`.

## 0. What is already in place

The Tokio-shaped parts that exist and pass: the work queue with a ring, a LIFO slot and an injected overflow;
the park/wake protocol with the notification inside the critical section that re-checks the predicate; the task
layer with `spawn`/`await` and continuation-passing; `blockOn` driving the executor on the caller's thread; and
the specification — a model whose transitions SC1–SC6 check and whose obligations are proved.

Measured, as of the benchmarks in the repository: parity with `Std.Async` on the batch shape at equal thread
count (17.5 ms against 16.5 ms per 10 000 units), **7.6× faster than a native `Task` on a dependent chain**
(924 ns against 6 987 ns per link), and ahead of the stock pool at its default configuration (1.6× throughput,
2.3× tail). The remaining per-unit gap on the batch shape is about 4×, and its source is allocation and CPS
indirection rather than scheduling.

## 1. Should io_uring be part of the design?

**No, and D11 already says why.** The short form, with the two additions this workplan makes.

D11's reasoning, which stands: io_uring is *not another extern* — its whole shape is two ring buffers mapped
into user space, so it **replaces the reactor rather than extending it**; it is **Linux-only**, where libuv buys
macOS and Windows for free; it is **disabled by default in some environments** (`io_uring_disabled`, kernel
6.6+, and container seccomp profiles); and it is **unstable even in Rust** (`--cfg tokio_unstable`, the
`io-uring` feature, `runtime/io/driver/uring.rs`). Every `lean_uv_*` call goes through the runtime's single
`global_ev`, so a ring would need new externs that bypass the leaf layer D3 reuses.

Two additions from what we have measured and built:

1. **It would not address what we are actually slow at.** Our measured deficit is per-unit allocation and CPS
   indirection (~4× on the batch shape). The reactor is not in that number: for sockets, epoll costs
   O(ready) rather than O(connections), and one reactor is not the bottleneck — D11's own argument. io_uring
   buys fewer syscalls and no thread pool for files, both real, neither touching our hot path.
1. **It is already isolated by the design.** D3's seam means an external event arrives at the inject queue
   regardless of what produced it, so an io_uring-backed leaf plugs in through the *same* adapter as a libuv
   one. The one thing it would change in the roadmap is a premise of W4: D11 says "for files a thread is the
   only option", and io_uring would make file I/O genuinely asynchronous — so the blocking pool should stay
   **bounded and separable**, a route that blocking leaves take, rather than file I/O being baked into it.

Two things argue the other way, and a decision record should carry them rather than only the costs.

**The seam is already shaped for it.** io_uring is *completion*-based: an operation is submitted with a
`user_data` tag and the completion carries that tag back — which is D3's seam literally, "an event attaches a
continuation that enqueues". epoll and libuv give *readiness* instead, leaving the operation to be issued and
re-armed by us. A ring-based leaf therefore fits this design better than a readiness-based one does.

**And it is the only route to a loop we own.** With libuv we cannot own the reactor at all: one process-global
`global_ev`, no `uv_loop_init` anywhere (D11) — structurally the same singleton the task manager has. A ring is
polled by whoever holds it, so a carrier could be scheduler *and* reactor on one thread, which is what Tokio's
`current_thread` actually is. That is a genuine argument for io_uring, and it is an argument for **owning the
leaf set**, not for swapping one reactor library for another.

Against: every leaf becomes ours, which is the premise D3 and W1 rest on; DNS stays blocking either way, since
io_uring has no resolver; it is Linux-only, and Linux *conditionally* — this development machine carries
`apparmor_restrict_unprivileged_io_uring`, so D11's hazard is live here rather than hypothetical; and no
`liburing` is installed, so even the helper library would be work.

So the workplan does not add an io_uring item. It adds a **constraint** and a **decision rule**: the leaf seam
must be completion-shaped, and the question is not which reactor to link but **whose leaves**. Reusing Lean's
means libuv comes with them, and a ring-based leaf can still join at the seam. Writing our own means io_uring
becomes the attractive choice for the set we would be writing anyway — starting with files, where libuv gives
us nothing at all.

## 2. Workplan

### W1 — The leaf seam, as library code

**Deliverable.** `LeanIn/Runtime/Leaf.lean`: `awaitTask`, `awaitPromise` and `awaitAsync` — the last being the
adapter from `Std.Async.Async α` (which is `BaseIO (MaybeTask α)`) to `LeanIn.Task.Async α` — promoted out of
the test client, with both directions documented: an off-carrier completion enqueues our resume, and our task
can await anything `Std.Async` produces.

**Why Tokio.** This is `wake() → inject.push` plus `async`/`await` on someone else's leaf. It is the seam
`interface.md` §4 describes, and the reason the leaf operations are not ours.

**Acceptance.** A scenario where an off-carrier completion wakes a *parked* carrier: the resumed step runs on
the carrier's thread, the completor's thread is observed to differ, and nothing of ours runs on it — SC6
generalised, with its detector control.

**Met.** `LeanIn/Runtime/Leaf.lean` holds `awaitTask`, `awaitPromise` and `awaitAsync`; SC6 is routed through
them rather than owning its own; and the boundary above is verified by grep — `Std.Async` appears nowhere in the
library outside that file.

One part of the item changed on contact, which is worth recording where the item is: there is **no `MonadLift`
instance** for `Std.Async.Async`, and there cannot be one as specified. A registration is a `Task` that has to be
kept alive, so the conversions take a registry the caller owns, and runtime-scoped state is not something an
instance can carry. They are explicit calls, and the finding sits with them.

Two smaller things settled by building. `awaitAsync` needs no `joinTask` — `toRawBaseIO` yields the `MaybeTask`
unwrapped — and the outbound direction was measured with W3's criterion early:

```
sleep   : 4 x 50ms via Std.Async on carrier 347780: 51ms (serial would be 200ms)
```

Four libuv timers overlapping on one carrier: the first time this runtime drives libuv, and the shape W3 has to
show for a timer to be a timer rather than a blocked thread.

**And a boundary that this item defines for the rest of the tree.** Today the runtime calls no `Std.Async`
anywhere — the only mention of it under `LeanIn/` is a comment — so it uses no libuv; the platform library is
in the build only because `Std.Internal` re-exports `Std.Async` publicly. This item is where that changes, and
it should change in exactly one place: after W1, `Std.Async` is referenced by the leaf module and by nothing
else, and a check in the suite can say so. Everything else in the runtime stays on the C++ primitives.

### W2 — Sockets

**Deliverable.** An accept loop and per-connection tasks over `Std.Async.TCP`'s `accept`/`recv?`/`send`,
reached through W1; a minimal `Runtime.serve`-shaped entry point.

**Why Tokio.** `TcpListener`/`TcpStream` and the accept loop are the floor of any network service.

**Acceptance.** A scenario: N concurrent connections, each echoed correctly, every step on the carrier,
`inFlight` back to 0 at the end. A measurement: connections per second and per-connection round trip, added as
rows so regressions are visible.

### W3 — Timers

**Deliverable.** `Runtime.sleep` and `withTimeout` over `Std.Async.Timer`.

**Why Tokio.** `sleep` and `timeout` are the two most-used leaves in real services.

**Acceptance.** The affirmative control that makes it a capability rather than a formality: N tasks each
sleeping `d` finish in about `d`, not N × d (`spike` already measures 64 × 100 ms at 102 ms for
`Async.sleep`), and a task spawned *while* another sleeps still runs.

### W4 — The blocking pool (PLAN.md M4)

**Deliverable.** `LeanIn/Runtime/Blocking.lean`: a bounded pool of carrier threads off the executor's queue,
with its own queue and shutdown, for the leaves that genuinely block: file I/O, the synchronous APIs
(`IO.FS`, `IO.sleep`), foreign or CPU-heavy calls. **Not DNS** — D11 records that `uv_getaddrinfo` runs on
libuv's own pool (`uv/dns.cpp:73`), so that leaf is already off-carrier, and Lean binds no general threadpool
API of its own to duplicate. The remit is narrower than "anything slow", and this is the line to check when a
leaf is added.

**Why Tokio.** `spawn_blocking` and `block_in_place`. It is also the only route to I/O concurrency we have,
since one carrier that blocks runs nothing else.

**Acceptance.** The plan's two cases as regression guards — N blocking jobs must not stall the executor, and
the stock pool must be left untouched — plus two existing rows that must move: `--runtime-tail`'s `queue` line
(2401 ms at one worker today; it should become about the blocker's duration) and the 4 × 25 ms sleep row
(100 ms → about 25 ms).

### W5 — The safety trio

**Deliverable.** Cancellation (dropping a task stops it being stepped and removes its registrations),
per-task error outcomes (`Task (Except …)`-shaped, or a supervisor — a malformed request must not panic the
runtime), and a `shutdown` that drains ring, slot and inject.

**Why Tokio.** A server cannot be written without any of the three: clients disconnect, handlers fail, and
processes get signals.

**Acceptance.** Three scenarios with their controls: a disconnect stops the work (a body's counter stops
advancing); one connection erroring leaves the others served; and after `stop`, in-flight work completes before
`run` returns, with `remaining = 0`.

### W6 — Async synchronisation and backpressure

**Deliverable.** `LeanIn/Task/Sync.lean`: an **async mutex** (the pieces exist — a `Join` cell is a waiter
queue and `resume` is the wake), an async semaphore, and a bounded channel.

**Why Tokio.** `tokio::sync::{Mutex, Semaphore, mpsc}`. State that spans an `await` cannot use a blocking lock
in a single-carrier runtime: the blocking version is the case that cannot be demonstrated because it wedges the
carrier.

**Acceptance.** Two tasks sharing a mutex across awaits both complete, and a task waiting on it does not stall
unrelated tasks; a flood scenario where the bounded queue holds and the accepted/rejected counts are exact.

### W7 — Selection, racing and priority

**Deliverable.** The interface decision on a `select`-shaped operation (`interface.md` §5 currently records the
absence), `race`/`join` combinators once it exists, and a priority argument on `spawn`.

**Why Tokio.** `select!`, `join!`, `JoinSet`, and per-task priority.

**Acceptance.** A scenario observing that the first of several handles to become ready is the one which wins,
and a priority scenario asserting the order the queue serves.

### W8 — Multi-carrier and stealing (PLAN.md M5), with O2

**Deliverable.** P carriers, per-worker rings behind their own locks plus the shared inject, park/unpark across
threads, and stealing with batch size one (D4). **O2 must close first**: Lean has no `Send`/`Sync`, so nothing
in the type system stops state from being shared across carriers, and the interface cannot be frozen until
something does.

**Why Tokio.** The multi-threaded scheduler, and the only route to using more than one core for CPU-shaped work
such as TLS, compression or JSON.

**Acceptance.** The plan's M5 exit criteria, the scheduler's three model obligations re-discharged for P
carriers, and two measurement conditions: the batch-shape gap to the native pool must shrink with P, and the
chain-shape advantage (7.6×) must not regress.

### W9 — The HTTP surface

**Deliverable.** Either `Std.Http.Server` driven by the runtime — the survey's own verdict is "reuse" — or a
minimal specified HTTP/1.1 if the project wants the protocol's own contracts.

**Why Tokio.** This is hyper/axum's role, and it is where "write a web server" actually lands.

**Acceptance.** An end-to-end scenario: a request over a real socket, a byte-exact response, and the framework's
behaviour contracts with their controls.

### P1, P2 — Two cross-cutting performance items

**P2 — the burst path, and it comes first.** Enqueuing into a saturated ring costs **1533 ns** against **169 ns**
steady, and the benchmark's batch shape spawns 10 000 units into a 256-slot ring — so its **1657 ns per task is
the overflow path almost exactly**. The batch shape is the ring, not the task machinery, which is what the
earlier attribution got wrong. The fix is a `Ring` primitive that moves the back half without draining the whole
thing, which the container cannot do today because it can only pop its front. Acceptance: `--runtime-ops` with
the burst row within about 2× of the steady one, and a benchmark row that *streams* rather than batches, since
the current one conflates the two and so cannot see this.

**P1 — allocation and CPS, and it is the chain-shape item.** The round trip is **588 ns**, of which ~169 ns is
the enqueue, so ~420 ns is cell handling, resumption and the bind chain — the part with no counterpart in a
compiler-generated state machine. Acceptance: the round-trip row, and `--runtime-bench` parity at equal thread
count on a streaming shape.

**Standing, for orientation.** At the default configuration this runtime is now ahead on both shapes measured:
16.6 ms against the native pool's 26.4 ms on the batch, and 588 ns against 5093 ns on a chain link. At *equal
thread count* it is still ~4× behind the native pool on the batch shape — and that gap is what P2 is for.

## 3. Where to start

W1 first, because it is ten to twenty lines and it unblocks every leaf at once — sockets, timers, DNS, channels
and `Std.Http` all sit behind that one type. Then P1, because a server is batch-shaped, which is the shape where
we are 4× behind rather than 7.6× ahead. Then W4, which is already the plan's next milestone and whose motive is
already measured. W5 and W6 are interface work the plan already knows about; W8 is the largest single piece and
gated on O2; W9 is mostly someone else's code, which is the point.

## 4. What stays absent

Unchanged from `interface.md` §5, and worth restating because a workplan invites scope creep: no bare `wait`
(A4 permits spurious wakeups), no fairness or priority *guarantee* (only a bound on the LIFO allowance), no
atomics in the interface, no `LocalSet`/`block_in_place`/runtime-flavour enum, and no io_uring backend of our
own — a ring would arrive as a leaf behind W1, if it arrives at all.
