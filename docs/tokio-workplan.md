# A Tokio-shaped workplan

What would have to be built, and what evidence would have to exist, before `leanin` is something you could
write a network service on. Ordered so that each item unblocks the next, with the Tokio-like aspects first.

This extends [`PLAN.md`](../PLAN.md) rather than replacing it: **W4 is its M4** (the blocking pool) and **W8 is
its M5** (multi-carrier and stealing). Everything else is new, and the milestone numbering here is deliberately
separate so the two can be read side by side.

Every deliverable states the artefact and the evidence that it is met. The evidence idiom is the repository's
own: a **scenario** at an external boundary with its controls, a **proof** against the model, or a
**measurement** from `--runtime-bench`, `--runtime-tail`, `--runtime-shared`, **measurement** from `--runtime-bench`, `--runtime-tail`, `--runtime-shared`, `--runtime-ops`, `--spike`,
`--runtime-async` (the rows compared against `Std.Async`) or `--runtime-unit` (one transaction, decomposed).

**The item numbers are names, not an order. §3 is the order**, and it is the one to read before starting: it
moves W5 ahead of W4 and interleaves the webserver items W10–W14 with the scheduler ones.

## 0. What is already in place

The Tokio-shaped parts that exist and pass: the work queue with a ring, a LIFO slot and an injected overflow;
the park/wake protocol with the notification inside the critical section that re-checks the predicate; the task
layer with `spawn`/`await` and continuation-passing; `blockOn` driving the executor on the caller's thread; and
the specification — a model whose transitions SC1–SC6 check and whose obligations are proved.

Measured, as of the benchmarks in the repository: **ahead of `Std.Async` on the batch shape at every thread
count** — 10.2–11.3 ms against 24.2 ms per 10 000 units at one worker, and against its 105–168 ms at eight,
where it degrades; **7.6× faster than a native `Task` on a dependent chain** (924 ns against 6 987 ns per
link); and ahead of the stock pool at its default configuration (1.6× throughput, 2.3× tail). The per-unit gap
to the native pool on the batch shape is closed, and what remains is allocation and CPS indirection rather than
scheduling (P1).

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

**Deliverable.** Our own accept loop and per-connection driving over `Std.Async.TCP`'s socket operations —
`Socket.Server.accept` and `Socket.Client.recv?`/`sendAll` — reached through W1, so every await is ours and
each accepted connection runs on a carrier. W10's survey moved the loop back into our hands: the shipped
`serve` runs its accept loop as a stock `Task` (`Server.lean:193`), and Lean's `Task` scheduler cannot be
replaced, so the loop that serves connections is ours even where the protocol is not. A `Transport` instance
over our socket is what keeps that loop independent of the socket type, and the channel-backed `Mock` instance
is what lets it be tested with no socket at all.

**Why Tokio.** `TcpListener`/`TcpStream` and the accept loop are the floor of any network service.

**Met.** `LeanIn/Runtime/Net.lean` holds the socket seam and the accept loop: `Listener.bind`/`accept`,
`Conn.recv`/`send`/`sendAll`/`shutdown`, `echoConn`, and `serveN`/`serveNJoin` — each one an `awaitAsync` over
`Std.Async`'s operation, so a completion enqueues our resume and nothing of ours runs on the completing thread.
The module opens nothing from `Std.Async`, because two of its names collide with ours — it has its own
`MonadAsync`, whose method is `async` where ours is `spawn`, and its own `background` — so it qualifies every
name on the far side of the seam and leaves ours alone. It is the boundary, and it reads like one.

SC7 is the scenario, and `--runtime-net`'s record is what it reads:

```
SC7 ok: connections=16 serverThreads=1 clientAmongServer=false echoes=16 heldBefore=3 inFlightAfter=0
SC7 control: rejected a second server thread, a carrier shared with the client, a leaked task and a missed reply
```

One distinct server thread for the accept loop and all sixteen connection tasks, on a thread the client is not
on, sixteen replies byte-identical, and nothing held once every connection has been awaited. The fixture holds
the detector to its own control — a second server thread, a carrier shared with the client, a missed reply, and
a task still held — and the executable reports its two detector controls in the same invocation.

**And one thing this item no longer claims.** It used to promise a `Std.Http.Transport` instance over these
sockets. It should not: that class is `Std.Async.Async`-typed, so an instance over these wrappers would hand a
driver a stock-typed value and put the work back on the pool. What this module defines is the socket shape a
driver of *ours* uses (`Conn`); the transport class belongs with the layer that drives it, which is the copy W15
describes.

**The measurement, and what it does not have.** `--runtime-net` reports sixteen concurrent connections in
4.8–6.9 ms of wall time on one carrier — roughly 2.3–3.3 k connections a second, against a client that is not
ours. It has **no baseline**, and that is honest rather than pending: a shipped-path echo server for the same
workload was written into the diagnostic and backed out, because its accept loop with a per-connection
`background` does not elaborate there. The comparison this row wants is W16's, where the server under the
harness is a variable by design; `docs/PERFORMANCE.md` carries the row marked as having no baseline rather than
leaving it out.

**Acceptance.** A scenario: N concurrent connections, each echoed correctly, every step on the carrier,
`inFlight` back to 0 at the end. A measurement: connections per second and per-connection round trip, added as
rows so regressions are visible.

### W3 — Timers

**Deliverable.** `Runtime.sleep` and `withTimeout` over `Std.Async.Timer`.

**Why Tokio.** `sleep` and `timeout` are the two most-used leaves in real services.

**Acceptance.** The affirmative control that makes it a capability rather than a formality: N tasks each
sleeping `d` finish in about `d`, not N × d (`spike` already measures 64 × 100 ms at 102 ms for
`Async.sleep`), and a task spawned *while* another sleeps still runs.

**Met.** `LeanIn/Runtime/Time.lean`: `sleep` over `Std.Async`'s timer through W1's seam, and `withTimeout` as
the race a timeout actually is. The item also carries one addition to the task layer, and it is the interesting
part: `Join.resolve` states that a handle has one writer and is loud when that is broken, which is right for a
normal completion and wrong for a race, where two writers are the design and one must lose — so
`Join.resolveFirst` is that second law, and it is the seed W7's select grows from.

SC8 is the scenario, and the reading is deliberately clock-free: **every one of the sixteen starts precedes the
first wake**, which is what "they finish in about `d`, not `N × d`" means once a clock is not allowed to decide
a check. A task spawned while all sixteen sleeps were pending ran before the first wake too, and the two timeout
outcomes are chosen so that neither depends on how long anything takes.

```
SC8 ok: sleepers=16 overlap=true lateBeforeWake=true wakes=16 timeoutHit=none timeoutMiss=some:7
SC8 control: rejected sleeps that occupied the carrier, a late task that did not run, a missed wake and either timeout outcome swapped
```

**The control earned its keep before the check did.** The first version of the overlap detector required every
event before the first wake to be a start, and the late spawn sits there — so it read `false` while the measured
block showed sixteen sleeps completing in 51 ms, and its own control reported that it would equally have
accepted a blocking-shaped order. The claim is "no start comes after the first wake", which is what the detector
now tests.

**What is left behind, stated.** A `withTimeout` that returns because its computation finished leaves its timer
pending until it fires: one parked task, and nothing else. Cancelling it needs a handle on the timer — the
`IO.Promise` and `Task` seam is where one would come from — and an operation that drops scheduled work, which
`Runtime.cancel` now is (W5). What is still missing is the timer's half, so a pending fire is still the loser's
write to ignore rather than a cancellation to make. What is *not* left untested is the loser's write:
`firstWins` and `lateTimerIgnored` in SC8's record are the first-writer law itself, the second of them with the
timer genuinely firing after the winner wrote — and the loud `resolve` in either position would raise out of the
driver instead, so reaching the record at all is part of that evidence.

**The comparison, and what it is against.** Sixteen 50 ms sleeps cost 51 ms on one carrier against **100 ms** for
the same sixteen sleeps run *concurrently* on the stock pool, one `IO.asTask` each — **1.9×, and it is one thread
against eight**. That number is the mechanism rather than a caveat: a blocking sleep occupies the worker it runs
on, so eight workers do two rounds of 50 ms, while one carrier parks and overlaps all sixteen. The same waits
issued *one after another* on one thread take 801 ms, and that reading stays in the table labelled as what not
overlapping costs rather than as a baseline. Against the shipped timer path the row is parity (51 ms against
`spike`'s 64 × 100 ms in 102 ms), cited rather than re-run, because the shipped timer fan-out does not elaborate
in the test client; the crossing is marked in `docs/PERFORMANCE.md`.

### W10 — The HTTP surface we would actually be reusing

**Deliverable.** A survey of `Std.Http.Server` and its neighbours under `Std/Http/`, answering what decides W9:
keep-alive and connection reuse, request-size and header limits, HEAD and the other methods, chunked
transfer-encoding, the timeout knobs, and — the one that decides most — *how it is driven*: whether it takes a
runtime to run on, or brings its own loop.

**Why.** W9 proposes reuse, and reuse is only a decision once the reused surface is known. If it cannot be run
on our carrier, or does not do limits or keep-alive, then W9 is a protocol implementation rather than an
integration, which changes the size of the largest webserver item. Read-only, and it can run beside W2.

**Acceptance.** A written answer, a line per question with a file-and-line anchor, and a verdict on whether W9
is integration or implementation.

**Met.** `Std.Http.Server` is a complete HTTP/1.1 server and the answer is **integration**.

| question | answer |
|---|---|
| how is it driven | it abstracts over a **`Std.Http.Transport`** class (`Std/Http/Transport.lean`): `recv`, `sendAll`, `recvSelector`, `close`, all `Async`-typed. `Socket.Client` is one instance and a channel-backed `Mock` another, so the transport is ours to choose |
| keep-alive | `Config.enableKeepAlive` (on by default), `maxRequests` per connection, `keepAliveTimeout` 12 s (`Std/Http/Server/Config.lean`) |
| limits | `maxConnections` 1024, `maxHeaders` 50, `maxHeaderBytes` 64 KiB, `maxUriLength` 8192, per-name and per-value limits, chunk limits (`maxChunkSize` 8 MiB), `maxBodySize` 64 MiB, `maxTrailerHeaders` |
| timeouts | `headerTimeout` 5 s, named in the source as the defence against slowloris, and `lingeringTimeout` 10 s for bodies, both `Time.Millisecond.Offset` |
| methods, chunked | `Data/Method.lean` and `Data/Chunk.lean`, with the H1 codec in `Protocol/H1.lean` (56 KB) and `Internal/ChunkedBuffer.lean` |
| shutdown | a `CancellationContext`, an `activeConnections` counter and a `shutdownPromise`: `shutdown`, `waitShutdown`, `shutdownAndWait`, and the promise resolves only when the count reaches zero — a drain, not a flag |
| limiting | a `Semaphore` acquired *before* `accept`, so the cap bounds accepted connections rather than queued ones |

The split is sharper than "integration", and the reason is that `Std.Async` is `BaseIO (MaybeTask α)` over
`Task`s. **`await` is a yield point, not a block** — `Basic.lean:471` hands the `Task` straight back to whoever
is driving. But `background` is `discard ∘ async` and `async` is `BaseIO.asTask` (`Basic.lean:463`, `:994`),
which is a task on the *stock pool*. The server spawns at exactly four places: the accept loop
(`Server.lean:193`), each connection (`Server.lean:182`), each handler call (`Connection.lean:157`, `:318`), and
a streaming body's generator (`Data/Body/Stream.lean:669`). Driving `serve` from one of our carriers would
leave the accept loop and every handler on the stock pool with our carrier stepping only the prologue — and no
hook exists to change that, since Lean's `Task` scheduler is not replaceable.

So what is reusable is the **library, not the driver**: `Protocol/H1.lean` is a pure machine (`feed`, `step`,
`send`, `pullBody`) with `Data/*` and `Config` beside it, and it drives no concurrency at all. W9 is that
machine plus a connection loop of ours, and W2 keeps the accept loop, because the shipped one is a stock task.
The limits, timeouts and drain that W5, W6 and W14 were partly for remain policy we inherit from `Config`.

### W11 — Buffered I/O helpers

**Collapsed into W9.** This item was written before W10's survey, and that survey removed its reason: the H1
codec buffers and frames its own bytes — it takes them through `feed` and reports events — so a driver feeds it
what `recv` returns and writes what `take` produced. The shapes a *router* or a *body helper* wants (`lines`, a
buffered writer, `split`) are application-level, and the two an HTTP *parser* would have needed are inside the
codec. Nothing is left to build here, and the item stays in the record rather than being deleted so the next
reader can see what replaced it.

**Deliverable.** The reading and writing shapes an HTTP parser assumes, over W1's leaves: `readUntil` against a
delimiter (the request line and the headers), `readExact`, `lines`, a buffered writer with `flush`, `copy`, and
`split` for half-close. `Std.Async.IO` today is three classes — `AsyncRead.read`, `AsyncWrite.write`/`writeAll`/
`flush`, `AsyncStream.next` — with no buffering, no delimiting and no splitting, so every parser written on it
hand-rolls all four.

**Why Tokio.** `AsyncBufReadExt::{read_until, lines}`, `read_exact`, `copy`, `TcpStream::split`, `BufWriter`.
This is the layer between the socket and the protocol, and it is small.

**Shrunk by W10.** The request line, the headers, chunked framing and their limits all live in the H1 codec
(`Protocol/H1.lean`, `Data/Chunk.lean`), so this item is only the shapes a router or a body helper needs on top
of them.

**Acceptance.** A scenario framing two messages with a delimiter that arrives across three writes, with the
split point inside the delimiter, plus the control that the same detector rejects a partial read taken as
complete.

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

**Met, and what the rows read.** The scenario is SC12, and it is green: four blocking
jobs submitted through the pool run on two threads that are not the carrier, a carrier step falls strictly
between the first job's start and its completion, the stock-priority task finishes before the jobs do, the
accounting reads four while they are outstanding and zero once the pool is shut down, and both workers exit —
`nix develop -c bash tests/executor-contract.sh SC12`, green on every run since the submission path landed. The
two rows moved as the acceptance asked, and each is recorded with its command in `docs/PERFORMANCE.md`. The
`queue` line's requirement is met by the `blockqueue` lines beside it in §5 (the stock line stays, as the
citation of the problem): the same 8 × 300 ms workload with
the blockers routed through the pool of eight finishes at ~300 ms — the blocker's duration, against the stock
line's ~2401 ms at one worker — and reads the same ~300 ms at `LEAN_NUM_THREADS=1`, because the blockers are
no longer on the stock pool at all. The 4 × 25 ms sleep row is met by `--runtime-bench`'s §4.1 row, which reads
~25.8 ms against the stock row's ~25.1 ms where its own record before the pool was 100 ms. What W4 does *not*
claim is W6's ground: a blocking lock held across an `await` still wedges the carrier, because moving work to
the pool does not make a blocking lock awaitable, and the pool is not a runtime flavour (`docs/interface.md`
§5 is unchanged).

### W5 — The safety trio

**Deliverable.** Cancellation (dropping a task stops it being stepped and removes its registrations),
per-task error outcomes (`Task (Except …)`-shaped, or a supervisor — a malformed request must not panic the
runtime), and a `shutdown` that drains ring, slot and inject.

**Cancellation safety** is the property a server actually needs, and it is not what dropping gives: a connection
cancelled mid-request must lose nothing and duplicate nothing, which is a statement about the task state machine
rather than about the queue. And **a parser must be total**: a panic in Lean is not catchable, so "a malformed
request must not panic the runtime" cannot be implemented as isolation around a handler — it is an obligation on
the parsing code, checked by the model rather than caught at the boundary.

**Why Tokio.** A server cannot be written without any of the three: clients disconnect, handlers fail, and
processes get signals.

**The error half is in.** `LeanIn/Task/Error.lean` is the channel `interface.md` §5 records as absent: `EAsync ε α`
is `Async (Except ε α)`, `bind` short-circuits on `error`, `throw`/`tryCatch` are the operators, and the handle
an awaiter receives is a handle on the failing computation. It is a layer *over* the task layer, so it needed no
new scheduling and no new resolution law. `Leaf.lean` gained `awaitTaskE`/`awaitPromiseE`/`awaitAsyncE` beside
the panicking conversions, and `Runtime/Net.lean` now uses them throughout — a socket failure is a value, because
a client closing a connection mid-request is the normal case for a server, and `echoConn` catches rather than
dying. The reachable defect is exact: the previous version took the process down when a client disconnected.
What this does *not* fix is a `panic!`, which aborts and stays fatal, so the totality obligation below stands.

**Its test.** SC9: a refused connect — error code 111 — arrives as a value, an accepted connect to the run's own
listener is `ok` as the affirmative control, and the listener is still bound when the record prints, with three
near misses held against the detector including an accepted connect that also failed.

Writing it turned the SIGSEGV that killed the first attempt into a rule. A socket's descriptor dies with the
*last use* of the Lean object that owns it, not at the end of its scope: the first version read the listener's
address immediately before connecting, and the listener was collected in between — so the connect was reset by a
socket that had served sixteen connections a moment earlier, and two of four runs died instead of printing.
Holding it in a reference whose own last use falls *after* the connect keeps both alive through it, and six
consecutive runs then read `refused=…111`, `accepted=ok` and a bound listener. The driver obeys this for its
listener and for every connection it serves, which is why it is recorded here rather than discovered there.

**The drain works, and the hang that hid it is worth recording.** `stop` used to *abandon*: `Runtime.blockOn` ended
the driver as soon as the pool was empty and the executor was stopping, and a stopped executor still holds work as
continuations registered on leaves — those are not in the pool by construction, since an awaited leaf yields and
queues nothing. So `Runtime.run` threw "the driver stopped before the computation finished", the connection's
continuation was never resumed, and a client waiting on it hung in `recv` for as long as a watchdog allowed. The
model's shutdown says *drain*; the driver aborted, and running the thing is what showed the difference. `blockOn`
now waits for work to appear rather than ending: `--runtime-drain` reads `stopping-before=false`,
`stopping-after=true`, `returned=true` with the loop's own value, and returns in 95 µs to 1.0 ms — the poll
interval bounding it, which is W7's absence showing through.

**The server-shaped half, and the second bug it found.** SC10 makes the connection *itself* stop the executor from
inside the body being served, so "a connection is in flight when the stop arrives" is true by construction rather
than by a race: the client connects, sends, reads its echo and closes, and the loop — which stopped accepting when
it noticed — waits for the connection it already has. A stop that arrives before the accept leaves the connection
in the backlog while the loop drains an empty list, and the client then waits for an accept that never comes; two
versions of that mode hung on exactly that, which is why the stop moved inside the body. The run reads
`served=1 echoed=yes inFlightAfter=0 pendingHooks=0`, in 0.6–1.9 ms.

`pendingHooks=0` is the field the model cannot state, and the reason this is a scenario rather than a diagnostic.
Draining is not only about the pool: a task parked on a leaf holds no pool item at all, so a driver that stops
there abandons the continuation without disturbing any counter — which is the abandon above. The fix for *that* was
itself wrong in a way only this shape could show. It parked the driver directly, without recording that it was
parking, and `submit`/`spawnBase` notify **only when `parked ≠ 0`** — so the driver slept with the loop's poll
timer pending, the timer completed and enqueued the loop's continuation, and nothing told the driver. It now sets
`parked` before waiting and clears it on waking, as `Executor.work`'s predicate does. Both bugs were in the driver
and neither in the sockets, and neither was visible from a stop that arrived with an empty pool: an empty pool is
exactly what the second one needed.

**Acceptance.** Three scenarios with their controls: a disconnect stops the work (a body's counter stops
advancing); one connection erroring leaves the others served; and after `stop`, in-flight work completes before
`run` returns, with `remaining = 0`.

The third is met by SC10, which reads the connection's own echo coming back *after* the stop and an empty pool when
`run` returns. The first is met by SC11, which reads a disconnect cancelling the work: the counter as it stood in
the cancelling step and again after the run returns, equal, so no step of a cancelled computation ran afterwards.
The second clause's half of that is the second connection SC11 serves *after* the cancellation — work the
cancellation did not touch is unaffected — while "one connection erroring leaves the others served" as its own
scenario is still to write. `panic!` totality is separate again, because a `panic!` aborts rather than raising.

**Cancellation is explicit, and dropping is not it.** The deliverable above says "dropping a task stops it being
stepped"; what exists is an operation on a handle. Two facts from the toolchain decide that. A task created by
`IO.bindTask` "will run even if the last reference to the task is dropped" (`Init/System/IO.lean:266-269`), so
dropping a registration is not cancellation; and Lean's only drop hook, `IO.CancelToken`'s finalizer, runs on a
finalizer thread, which cannot carry the deterministic abort law SC11 asserts. Drop-driven cancellation is a stated
non-goal of this milestone rather than an omission, and the status row says so.

### W6 — Async synchronisation and backpressure

**Deliverable.** `LeanIn/Task/Sync.lean`: an **async mutex** (the pieces exist — a `Join` cell is a waiter
queue and `resume` is the wake), an async semaphore, and a bounded channel.

**Why Tokio.** `tokio::sync::{Mutex, Semaphore, mpsc}`. State that spans an `await` cannot use a blocking lock
in a single-carrier runtime: the blocking version is the case that cannot be demonstrated because it wedges the
carrier.

**What is missing, and what is not.** `Semaphore.acquire` returns an `IO.Promise`, `Channel.send`/`recv` return
`Task`s, and `Broadcast`/`Notify`/`CancellationToken` are the same shape — so those arrive across W1's seam as an
ordinary `await`, because a `Promise` or a `Task` *is* the waker substrate. What does not cross is the **OS-lock
family** — `Mutex`, `RecursiveMutex` and `SharedMutex` are real C++ locks, so taking one blocks the carrier —
and anything whose only interface is a blocking call. All three of the mutex, the semaphore and the channel are
built on the task layer's own `Join` and `ctx.resume` — *not* as adapters over `Std.Sync` — and the reason the
adapter route is rejected is recorded with the milestone below.

**Acceptance.** Two tasks sharing a mutex across awaits both complete, and a task waiting on it does not stall
unrelated tasks; a flood scenario where the bounded queue holds and the accepted/rejected counts are exact.

**Met, and the premise it corrected.** `LeanIn/Task/Sync.lean` holds the async mutex, the async semaphore and
the bounded channel; the scenario is SC13, green on every run —
`nix develop -c bash tests/executor-contract.sh SC13`, whose record reads two holders' sections non-overlapping
with an unrelated step falling strictly inside the first, the accepted/rejected counts exact against a bound of
two with an affirmative control in the same run, and every parked send delivered. The three cancellation laws
are read through non-parking probes (`tryLock`/`trySend`/`tryRecv`), so no assertion about a primitive depends on
a watchdog. The milestone's measurement rows are `--runtime-sync`'s `syncbench|` line, recorded with their
command in `docs/PERFORMANCE.md`; the primitive's classification and the rejected adapter route are in
`docs/decisions.md` D14 and in the module prose.

The premise at the end of "what is missing" — "the semaphore and the channel are adapters over what exists" — is
**wrong**, and this milestone is what disproved it. Both stock shapes hand what a waiter asked for to that
waiter *irrevocably*: `Std.Sync.Semaphore.release` dequeues a waiter and resolves the promise it parked on
(`Std/Sync/Semaphore.lean:76-87`), so the permit is gone whether or not that waiter ever runs again, and
`Std.Sync.Channel.recv` dequeues the message into the `Task` it returns (`Std/Sync/Channel.lean:542-546`),
before any awaiter is resumed. Our cancellation gate is `Item.fire` (`LeanIn/Task/Basic.lean:99-100`), which
skips a cancelled computation's step — but it cannot un-resolve a promise or re-enqueue a dequeued message, so a
waiter whose token is set between the hand-off and its resumed step has consumed a permit or a message and is
never granted it. The deliverable is therefore *our* mechanism on the task layer: an operation registers a fresh
`Join`, parks on it, and **acquires in its own step** when woken, so a wake is only a hint and a skipped wake
transfers nothing. An adapter could not satisfy that law, which is why it is rejected rather than layered over.

**What it does not bound.** D13's blocking-pool backlog stays unbounded, and `submit` stays O(queue length). W6
supplies the mechanism a bounded pool would use — a semaphore with a capacity — but back-pressuring `submit`
changes its signature and `spawnBlocking`'s shape and changes SC12's accounting, and it is a different
observable that needs its own scenario. It is therefore a separate item, now unblocked by W6, and D13's row says
so.

### W7 — Selection, racing and priority

**Deliverable.** The interface decision on a `select`-shaped operation (`interface.md` §5 currently records the
absence), `race`/`join` combinators once it exists, and a priority argument on `spawn`.

**Why Tokio.** `select!`, `join!`, `JoinSet`, and per-task priority.

**Acceptance.** A scenario observing that the first of several handles to become ready is the one which wins,
and a priority scenario asserting the order the queue serves.

### W12 — Task-local context and a connection registry

**Deliverable.** A task-local store — a request id, a deadline, a tracing context, read without threading it
through every signature — and a `JoinSet`-shaped set of handles that can be awaited as a group and drained.

**Why Tokio.** `task_local!` and `JoinSet`. The registry is what makes shutdown a *drain* — stop accepting, let
outstanding connections finish, cancel what outlives the deadline — rather than a counter check; the locals are
what make a log line say which request it belongs to.

**Acceptance.** A scenario where a value installed on the client task is read from a task it spawned on the
carrier, and not from a task on another carrier; a drain scenario where `shutdown` returns only after the
outstanding handlers have finished, with the live count observed to fall to zero.

**Met, and what its record reads.** Both deliverables are in. `LeanIn/Task/Basic.lean` carries the `Local`
record — a request id, a deadline and a tracing context — as a field of `Ctx`, with `Async.local` and
`Async.withLocal`, and `Async.spawn` copies the parent's local into the child's `Ctx`, so a spawned computation
inherits the innermost enclosing value at its spawn site. `LeanIn/Task/Registry.lean` is the `JoinSet`-shaped set
of handles (`new`, `add`, `spawn`, `size`, `joinAll`, `drain`), and `Net.lean`'s serving loops use it — `joinAll`
in `serveNJoin`, `drain` in `serveUntilStopped`/`serveBoundedLoop` — so shutdown is a drain *operation*.
The scenario is SC15, green on every run —
`nix develop -c bash tests/executor-contract.sh SC15`, which invokes `lake exe controls --runtime-registry` three
times and asserts the same fields in each. One invocation's records read
`scope=7 child=7 unrelated=0` (the value installed on the client computation is read by the computation it
spawned and not by one it did not), `heldBefore=4 completions=3 completedAtDrainReturn=3 liveAtDrainReturn=0
heldAfter=0` (the drain returned only after the outstanding handlers finished, with the live count at zero) and
`cancelOutcome=error` (a cancelled handle neither hangs the drain nor is granted to a caller). The milestone's
measurement rows are `--runtime-registry`'s `registrybench|`/`registryhand|`/`registryheld|` lines, recorded with
their command in `docs/PERFORMANCE.md` §3.2; the design, the deferred deadline arm and the argued model
obligation are in `docs/decisions.md` D16 and the module prose.

**Two limits, recorded rather than hidden.** The clause's second half — "and not from a task on another carrier"
— is not observable, because the runtime is single-carrier (D2) and W8 has not landed; it is rendered as the
inheritance/non-inheritance pair on one carrier, `carrierCount=1` names the deferral, and the cross-carrier half
is **W8's**. And "cancel what outlives the deadline" is not tested: it needs W13's harness clock, since a
wall-clock test of it is a sleep. The registry is **unbounded by decision** — a `JoinSet` holds handles and does
not meter admissions — so it is *not* D13's blocking-pool answer, and D13's row carries that correction.

### W13 — Runtime handle, metrics, and deterministic time

**Deliverable.** A handle that spawns onto a running executor from a thread that is not a carrier (a signal
handler, a plain `IO.asTask`); a small set of counters (ready work, parked carriers, busy time per carrier); and
a mode where time is driven by the harness rather than the clock, so a timeout is tested at a stated instant
instead of by sleeping.

**Why Tokio.** `Handle::spawn`, `Runtime::metrics`, `#[tokio::test(start_paused = true)]`. The handle is what
lets a signal handler ask the runtime to stop; the counters are what capacity claims are argued from; and
without the third, every timeout and every shutdown deadline can only be tested by wall-clock luck, which is
what this repository accepts nowhere else.

**Acceptance.** A scenario where a non-carrier thread spawns and the work runs on a carrier; a shutdown driven by
a registered signal, observed to stop accepting and then drain; and a timeout test whose elapsed time is read
from the harness clock, with the control that the same test at a shorter deadline trips.

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

**Deliverable.** The protocol **reused, the driver ours**. `Std.Http.Protocol.H1`'s `Machine` is pure —
`feed`, `step`, `send`, `pullBody` — with `Data/*` for the typed messages and `Config` for the limits and
timeouts, so parsing, framing, keep-alive, chunking and every limit are not written twice. The connection loop
is ours, because the shipped one spawns stock `Task`s: accept, feed the machine from `Transport.recv` /
`recvSelector`, dispatch each `H1.Event` to a handler shaped like `Std.Http.Server.Handler`, and write the
machine's output back with `Transport.sendAll` — with every await being ours, so a handler runs on a carrier
and the connection can be cancelled when the client goes away.

**Why Tokio.** This is hyper/axum's role, and it is where "write a web server" actually lands.

**W10 decided the split**: the protocol is reused and the driver is ours, because the shipped connection
loop's `background`/`asTask` calls put the accept loop and every handler on the stock pool.

**Acceptance.** An end-to-end scenario: a request over a real socket, a byte-exact response, and the framework's
behaviour contracts with their controls.

### W14 — The service's own refinement statement

**Deliverable.** The obligations a *server* has, stated in the model and checked against the executor: every
accepted connection is either completed or closed and never silently dropped; the number of live connections
never exceeds its bound; and every request gets a response or an error within its deadline.

**Why.** The scheduler's obligations are the mechanism; these are the product, and they are what makes this
different from using `Std.Async` directly.

**Acceptance.** Each obligation as a scenario at the executor boundary with its control, alongside the model
statement it refines, in the shape SC1–SC6 already use.

**Met, and what its record reads.** The three obligations are proved over `LeanIn/Model/Service.lean`'s
`Service.Reachable` (`Service.NoDrop`, `Service.Bounded`, `Service.RequestsResolved` and
`Service.PendingWithinLive`, beside `Service.WF`, each with its per-transition preservation, its reachable
projection and a breaking-control), the library product is `Runtime.serveBounded`, and the scenario is SC14,
green on every run since the bound landed — `nix develop -c bash tests/executor-contract.sh SC14` invokes
`lake exe controls --runtime-service --bound=2` three times and reads
`SC14 ok: bound=2 accepted=[0,1,2,3,4] completed=[0,2,4] closed=[3,1] liveHighWater=2 parkedAtPeak=2 responded=[0,2,4] errored=[3,1] deadlineFired=yes`
— **one instance** of the record, not *the* record: the lists' orders (`closed=[3,1]`, `errored=[3,1]`) are the scheduler's, so only the id multisets are fixed —
with the three clauses SC14-O1/O2/O3 each bound to its own record fields and the detector's near misses rejected
in the same invocation. The red it replaced was **found, not arranged**: the shipped accept loop admits
unconditionally, so SC14-O2 failed on production with `liveHighWater=5` against `bound=2`, and the same run's
`accepted=[0,1,2,3,4]` shows the violation was already there. The refinement is the sanctioned fallback — a
proved model, an argued correspondence and an executable correspondence test (`docs/interface.md` §6,
`docs/decisions.md` D15) — and two limits are recorded there rather than hidden: only the success-path permit
release is exercised by SC14 (the wrapper's error branch is total by construction, not by observation), and a
cancelled body's release step is skipped by `Item.fire`, so a permit can leak — a liveness cost that reduces
admissions, not a breach of the bound. The measurement row is in `docs/PERFORMANCE.md`.

### W15 — Ask upstream to parameterise the async surface by its runtime

**Deliverable.** A proposal, and if it is accepted a patch, removing the two concrete couplings that keep
anything written against `Std.Async` from running on our carriers: `background`/`async` bottoming out in
`BaseIO.asTask` (`Std/Async/Basic.lean:463`, `:994`), and `Selector`, `CancellationContext` and the channel
type being concrete rather than class-shaped. `interface.md` §4 already expects half of this — `MonadAsync` and
`MonadAwait` instances over either implementation — so what is missing is a `MonadSelect`-shaped class beside
them and a driver generic over all three.

**Why.** If the surface is parameterised, `Std.Http.Server` runs on our executor with no fork of it and no driver
of ours, and milestone 0's "no hook to replace `Task`'s scheduler" stops mattering for every piece of code
written against the classes rather than against `Task`: nothing calls `asTask`, so nothing needs the hook.

**Why it gates nothing.** Upstream review has no delivery date, so W9's driver is written either way. If this
proposal lands, that driver is deleted rather than kept beside the shipped one.

**What the switch-out needs, precisely.** Feature parity is not the precondition; two *seams* are. Upstream, the
driver has to stop naming the concrete `Async`, `Selector`, `CancellationContext` and channel types —
`MonadAsync` and `MonadAwait` already exist, and the missing piece is a select-shaped class beside them. On our
side that class needs an instance, which means the select operation `interface.md` §5 records as absent (**W7**)
has to exist first, with the instances for our task type following it. The runtime *behaviour* the driver
relies on is the parity that actually matters, and it is a short list to check one by one: cancellation
propagating when a task is dropped, the select itself, notification, and the drain at shutdown — the last two
of which the model already proves.

**The local route, and what it costs.** If upstream latency is unacceptable, the same change can be made first
in a *namespaced copy* of the modules in question — the precedent is `Vendor/tokio/`, which is a read-only copy
kept for reference. A copy is editable, so the driver becomes generic here first and the upstream proposal
follows. The costs are real and belong in the decision: it must be renamed so it cannot collide with the
toolchain's `Std.Http`, it must be re-diffed whenever the toolchain moves, and it is a fork to be **deleted**
once upstream lands rather than kept beside it.

**Acceptance.** For the proposal, a written design and a maintainer's reply. For a patch, the evidence W1
produced for its own boundary: the same driver source typechecks against both `Std.Async`'s types and ours.

### W16 — The HTTP workload, measured on both backends

**Deliverable.** A benchmark of the *server* shape, built so the server under it is a variable rather than part
of the harness: a client-side row — requests per second, and per-request latency at the median and at the tail
— that takes a server address, plus a baseline produced today against the shipped `Std.Http.Server`. The
workload is fixed and written down: connection count, request count, whether connections are kept alive, and
the response body. A row whose shape changes between runs compares nothing.

**Why.** The reason to make the copy is to run the same server on this runtime, and the only evidence that it
does is the same harness pointed at both. The client is deliberately *not* ours: it drives TCP over the shipped
async layer, so the single thing that differs between the two runs is the server's runtime.

**Acceptance.** The baseline row against the shipped server, reproducible from one command; then, once the
vendored driver exists, the same command against this runtime, differing only in the address it is given. The
figures enter `docs/PERFORMANCE.md` at that point and not before — that document carries measured rows only.

### P1, P2 — Two cross-cutting performance items

**P2 — the burst path (landed).** Enqueuing into a saturated ring costs **1533 ns** against **169 ns**
steady, and the benchmark's batch shape spawns 10 000 units into a 256-slot ring — so its **1657 ns per task is
the overflow path almost exactly**. The batch shape is the ring, not the task machinery, which is what the
earlier attribution got wrong. Two things fixed it, both measured on this machine with the same command:
`Ring.keepFirst` moves the live count so the newer half leaves without the ring being read out and refilled
(24 656 µs → 16 550 µs), and a transaction releases the cell's hold on the state before it modifies the pool,
so the ring's slots are uniquely owned and `Array.set` does not copy them (16 550 µs → 10 987 µs). The row is
now 2.2× the same workload's `Std.Async` figure at one thread (24 179 µs) and 13× its figure at eight
(143 558 µs), and `Executor.submit` is 1 118 ns against 2 014 ns. The take side reaches the same
place by asking the scheduler before it reads the pool, so a refusal never modifies anything; its effect on
this row is small, because these takes mostly find the LIFO slot, which touches no slot array.

**P1 — allocation and CPS, and it is the chain-shape item.** The round trip is **588 ns**, of which ~169 ns is
the enqueue, so ~420 ns is cell handling, resumption and the bind chain — the part with no counterpart in a
compiler-generated state machine. Acceptance: the round-trip row, and `--runtime-bench` parity at equal thread
count on a streaming shape.

**Standing, for orientation.** This runtime is ahead on both shapes measured: 10.2–11.3 ms against the native
pool's 25.7–28.5 ms on the batch, and 588 ns against 5093 ns on a chain link. At *equal worker count* the batch
row is ahead too — 10.2–11.3 ms against `Std.Async`'s 24.2 ms at one thread — so what remains is allocation and
CPS indirection, which is P1.

## 3. The order

| # | step | state | unblocks |
|---|---|---|---|
| 1 | **W1** leaf seam | met | every leaf — sockets, timers, DNS, channels, `Std.Http` |
| 2 | **W10** the `Std.Http.Server` survey | met | whether W9 is an integration or an implementation |
| 3 | **W2** sockets | met (SC7) | any service at all |
| 4 | **W3** timers | met (SC8) | timeouts, deadlines, keep-alive |
| 5 | **W11** buffered I/O helpers | collapsed into W9 — the codec frames and buffers its own bytes | — |
| 6 | **W5** safety trio, and cancellation safety | the error channel is in (SC9), a stop drains a connection in flight (SC10), and a disconnect cancels the work (SC11) — by an explicit operation rather than by dropping; `panic!` totality to go | operability: disconnect, failure, signal |
| 7 | **W4** blocking pool | met (SC12) | file I/O, sync APIs, CPU in a handler |
| 8 | **W6** async sync and backpressure | | shared state, connection limits |
| 9 | **W14** the service's own refinement | met (SC14) | the product |
| 10 | **W12** task-locals, connection registry | met (SC15) | log context, drainable shutdown |
| 11 | **W7** selection, racing, priority | | racing a request against its deadline |
| 12 | **W13** handle, metrics, deterministic time | | operating it, capacity, timeout tests |
| 13 | **W8** multi-carrier and stealing (O2 first) | | more than one core |
| 14 | **W15** parameterise the async surface upstream (parallel, gates nothing) | | W9's shape |
| 15 | **W9** the HTTP surface | | a web server |
| 16 | **W16** the HTTP workload on both backends (needs W9 and the copy) | | the server row |
| 17 | **P1** allocation and CPS (P2 landed) | | the benchmark rows |

W1 is met, so the order starts at W10 and W2. W10 is read-only and can run beside W2; W2 and W3 give a service
that answers a request; W11 gives it framing; W5 makes it operable (disconnect, failure, signal); W4 unblocks any
handler that must touch a file or a CPU; W6 covers shared state and limits; W14 states what the service promises;
W12 makes it observable and drainable; W7 races a request against its deadline; W13 makes it operable and its
timeouts testable; W8 is the largest single piece and gated on O2; W9 is mostly someone else's code, which is the
point; P1 is what the last measurement row is for.

## 4. What stays absent

Unchanged from `interface.md` §5, and worth restating because a workplan invites scope creep: no bare `wait`
(A4 permits spurious wakeups), no fairness or priority *guarantee* (only a bound on the LIFO allowance), no
atomics in the interface, no `LocalSet`/`block_in_place`/runtime-flavour enum, and no io_uring backend of our
own — a ring would arrive as a leaf behind W1, if it arrives at all; and no panic isolation, because a panic is
not catchable in Lean, so totality of the parsing code is the defence rather than a supervisor around it.
