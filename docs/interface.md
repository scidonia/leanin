# The interface

Fixed before either implementation (D5). Two realisations of the same spec: a **pure model** that is
provable by ordinary sequential reasoning, and a **concurrent implementation** over the primitives in
[`primitive-theory.md`](primitive-theory.md). The obligation between them is refinement.

The interface exists to be *small*. Everything provable should be provable about the model.

______________________________________________________________________

## 1. Shape

```
Queue α     push / pop / steal            -- work
Scheduler   spawn / wake / inject / park / shutdown / blockOn
Task α      await                         -- plus MonadAsync / MonadAwait instances
```

`spawn` and `await` are the user surface; `push`/`pop`/`steal`/`park`/`wake` are mechanism. Five
mechanism operations plus the protocol, and nothing else — anything that cannot be expressed here is
out of scope, not a missing feature.

______________________________________________________________________

## 2. Queue

### The abstract model

```lean
abbrev Queue (α) := List α        -- oldest at the head
```

Pure, obviously correct, and the thing all properties are stated against:

| Operation | Model | Order |
|---|---|---|
| `push q x` | `q ++ [x]` | appends at the back |
| `pop q` | `(q.head?, q.tail)` | owner takes from the **front** |
| `steal self victim` | moves `victim.head?` to the back of `self` | thief takes from the **front** |

### The order is FIFO, and that is deliberate

This is worth stating explicitly because the folklore is wrong. Tokio's local run queue is **not** a
LIFO work-stealing deque: the owner `push_back`s and `pop`s from the front — FIFO — and a thief takes
a batch from the *same* end (`queue.rs:188`, `:361`, `:472`). The locality that a LIFO deque would
give is recovered instead by a **separate one-slot LIFO buffer**, drained between run-queue pops,
capped at `MAX_LIFO_POLLS_PER_TICK = 3` (`worker.rs:265`, `:713`) so that a two-task ping-pong
("A notifies B, B notifies A") cannot starve the queue.

So the implementation-side structure is:

```
WorkerQueue α  =  { ring : BoundedRing α   -- FIFO, capacity 256, overflow to inject
                  , lifo : Option α        -- owner-local, unsynchronised, checked first
                  , lifoPolls : Nat        -- reset each tick, capped at 3
                  }
```

`lifo` is owner-local in Tokio and stays owner-local here: it is inside the worker's own critical
section, never stolen, and is moved back into the ring before a worker gives up its core
(`worker.rs:479–481`).

### Bounded, with overflow

Capacity 256; when full the owner moves **half** the ring to the inject queue, and when a steal is in
flight it pushes only the new item there (`queue.rs:188–260`). Boundedness is the point: a fixed
array has no reclamation problem, which is the entire reason Tokio abandoned Chase–Lev
(`queue.rs:63`, and the blog's account).

### Invariants the model must state

**Realised** as `LeanIn.Model.Pool` (`LeanIn/Model/Pool.lean`): the worker shape sketched above, as
Lean. Invariants 1 and 5 are proved there — `Pool.Consistent` for no-lost-work, `submit_bounded` for
capacity, and `take_returns_if_present` for the LIFO allowance not stranding work. Invariants 2–4
(well-defined reads, uniqueness, existence) are stated over the pool as a whole and still to do.

⚠️ **`ring` here is the specification, not the container** (D12). It is the ghost view; a `Ring`
container — a fixed-size **`Array`** of slots plus a head index and a live count — refines it, with
`Ring.toList` as the view and `Ring.WF` (including density: the live range has no holes) as the
invariant. `Array`, not `List`, because `Array.set` updates in place while `List.set` copies; the
`List` lives only in the ghost view. Lean's own `Std.DHashMap` does exactly this: Array
implementation, `List` model, laws in a separate file.

Taken from the deque literature (Lê et al.'s four properties) and from Tokio's own assertion that a
queue is empty when dropped (`queue.rs:571`):

1. **No lost work.** Dropping a non-empty queue is an error, not a silent discard.
1. **Well-defined reads.** Only pushed elements are returned.
1. **Uniqueness.** An element is returned at most once, across `pop` and every `steal`.
1. **Existence.** With finitely many pushes, if takers keep attempting, every element is returned
   exactly once.
1. **Bounded capacity.** The ring never exceeds 256 and overflow routes to inject, never to `none`.

**Batch size is one here, and this is the one place we invert Tokio deliberately.** Batching amortises
a CAS and never blocks the victim; under a lock it lengthens the critical section *and* blocks the
victim (D4). Take one element.

______________________________________________________________________

## 3. Scheduler

```lean
structure Scheduler where
  workers : Array WorkerQueue        -- one ring per worker, each behind its own Mutex
  inject  : WorkerQueue              -- shared, receives overflow and external wakes
  idle    : IdleSet                  -- which workers are parked
  stopping : Bool
```

Protocol, stated as the obligations it must meet rather than the calls it makes:

| Operation | Obligation |
|---|---|
| `spawn s f` | enqueue on the current worker's queue (or inject if called from outside), then wake |
| `wake s w` | if `w ∈ idle`, remove it and unpark it; the state change and the notification happen under the same lock |
| `inject s f` | enqueue into `inject`; used for external events (D3) and overflow |
| `park s` | park only if the local ring, the LIFO slot and `inject` are all empty and `stopping` is false |
| `shutdown s` | set `stopping`, notify all, drain |

Three obligations, each traceable to an axiom:

- **No lost wakeup** — forced by A5 (notifications are not queued): a worker must not be able to
  observe "no work" and park between another thread's push and its notify. Solved the same way Tokio
  does, by doing both under one lock.
- **No lost work at shutdown** — forced by invariant 1 above. `shutdown` drains both `inject` and every
  ring before returning.
- **Bounded work per tick** — the coop budget, so one task cannot monopolise a worker. Not a
  correctness property; it is a *policy* with a stated bound, and the LIFO cap is the same kind of
  thing.

Two details that are policy, not mechanism, and are separately testable: the LIFO cap of 3, and the
inject check interval.

______________________________________________________________________

## 4. Task layer

Ours (D3), because `Std.Async` cannot be reused — it is `BaseIO (MaybeTask α)` and every operation
delegates to `Task` (`Basic.lean:327,389,432,456,463,474`).

```lean
structure Task (α : Type) where       -- a handle: its join cell and its cancellation token
structure Async (α : Type) where ...  -- a scheduleable computation, given its own token and its scheduling function
```

with instances so that generic code works over either implementation:

```lean
instance : MonadAsync Task Async
instance : MonadAwait Task Async
```

**Cancellation is part of the layer.** A handle carries a token, and cancelling it states and delivers two things:
**no step of a cancelled computation runs after the cancellation is requested**, and **an awaiter of a cancelled
handle is woken with the cancellation exactly once, immediately**. The first is enforced where a step is run — the
executor's item — rather than polled by the computation, because a leaf cannot be cancelled (the runtime runs a
`bindTask`-created task even when its last reference is dropped) and a computation that never checks must stop
anyway. The second is `resolveFirst`: a computation that has already produced its value keeps it, so a cancellation
never replaces a value that exists, and one that arrives first is delivered once. Registration entries carry the
token of the computation that left them, so a cancellation retires its own work's entries rather than only stopping
new steps from being scheduled.

**A cancellation does not reach a child.** Each spawned computation has its own token, and an item a child schedules
carries the child's token, so cancelling a parent leaves it running — `abort` rather than structured cancellation. A
computation that wants its children to stop with it has to cancel them.

`concurrently` and `background` are then written **once, generically**, against
`MonadAsync`/`MonadAwait` — which is the point of the classes existing, and they are the two combinators this
pair of classes can in fact express. `Async` here is **continuation-based** (`await` registers a continuation
and yields; it never blocks a thread), which is what makes a single-carrier executor possible at all.

**`select` is the operation, and it is the first-ready one.** `LeanIn/Task/Basic.lean` gives the layer
`select (h : Task α) (hs : List (Task α)) : Async (Nat × α)` — homogeneous, and non-empty: `h` is the head, so
index `0` names it and index `i+1` names `hs[i]`, and a zero-handle `select` is unrepresentable rather than a
meaningless `none`. It returns the winner's index *into the list as given* and its value, and it **detects
readiness, not order**: one shared `Join (Nat × α)` is registered on every handle through `Join.onReady`, each
continuation carrying its index, and the winner is the first `Join.resolveFirst` — so a handle that became ready
earlier but was reached later in the list still wins. Among handles already resolved when `select` is reached the
earliest in list order wins; among handles resolved while it waits, the first resolution wins. It **cancels
nothing**: a `Task` is a value whose cell is the value's home, so a handle passed to `select` is still awaitable
elsewhere, and a caller that wants the rest can keep them. `join (hs : List (Task α)) : Async (List α)` is the
all-of companion (`hs.mapM Async.await`, `join [] = pure []`); the pair case stays `concurrently`.

**`race` cancels its losers, and it is a runtime combinator.** `Runtime.race (hooks : Hooks) (v : α) (h : Task α)
(hs : List (Task α)) : Task.Async (Nat × α)` is `select` followed by `cancel hooks t v` for every non-winner. It
lives in the runtime because cancelling needs `Hooks` to retire a loser's leaf registrations and the task layer
has none. Of a cancelled loser a caller observes exactly W5's laws: its cell resolves with `v` exactly once and
immediately, no step of it runs afterwards, and its registrations are retired; a loser that finished *before*
the race returned keeps its own value, because a cancellation never replaces a value that exists. There is no
second abandonment mechanism — `race` is `select` composed with the existing `Runtime.cancel`.

**A priority argument on the runtime's outside spawn, and it promises nothing.** `Runtime.spawn (e : Executor cap)
(prio : Priority) (a : Task.Async α) : IO (Task.Task α)` takes `Priority.high`/`Priority.normal`, which select a
*placement lane*: `.high` places the task's first step in the owner-local one-slot LIFO buffer
(`Executor.spawnBase` → `Pool.spawn`), `.normal` appends it to the FIFO ring (`Executor.submitBase` →
`Pool.submit`). The slot is served before the ring while the tick's allowance lasts, so a `.high` spawn issued
after a `.normal` one is served first — but the argument is a placement request and nothing more; §5's
no-fairness-or-priority bullet governs it, and "high" promises only that the task is placed where the queue
serves sooner, never that it runs sooner. The register is unchanged: `select`/`join` use `Join`'s existing
operations and `ctx.resume`, `race` reuses `Runtime.cancel`, and `spawn`'s two destinations already exist — no
new primitive, no new extern, no new direct promise call (D17).

**Leaf operations are not ours.** Timers, sockets, DNS, signals and processes stay in `Std.Async` and
are reached across one bridge: an external event attaches a continuation that pushes into `inject`
and notifies — Tokio's `wake()` → `inject.push` + `unpark`
(`scheduler/current_thread/mod.rs:734`). Our task bodies are never `Task`s. *This bridge is D3/O3, and it is built:
`Runtime/Leaf.lean` is the whole of it, and SC7, SC9 and SC10 drive it at the public executable.*

**Blocking work gets off the carrier through a pool.** `Runtime.spawnBlocking (p : BlockingPool) (hooks : Hooks) (act : IO α) : Task.Async α`
submits `act` to a `BlockingPool` — a bounded set of worker threads off the executor's queue, with its own
queue and its own shutdown — and returns the ordinary `Task.Task α` this layer gives a spawned computation, so
`await`, `Runtime.cancel` and `concurrently` work on a blocking job with no new handle type. Its step registers
the job's liveness witness in `Hooks`, so `Runtime.pending` counts a blocking job exactly as it counts a leaf
registration; the completion is delivered as an item on the carrier through `ctx.resume`, and `Item.fire` skips
it when the submitting computation was cancelled. `spawnBlockingE` is the failure-carrying sibling
(`Task.EAsync IO.Error`), in `Runtime/Leaf.lean`'s `awaitTask`/`awaitTaskE` shape. The pool's threads come from
`Task.Priority.dedicated` (D13), so the layer gains a route rather than a primitive. *This is D13's design, and
it is built: `Runtime/Blocking.lean`, and SC12 drives it at the public executable.*

**Synchronisation is ours, and it guards no value.** `LeanIn/Task/Sync.lean` gives the task layer an async
mutex, an async semaphore and a bounded channel. `Mutex.lock`/`unlock` and `Semaphore.acquire`/`release` park
the *computation*, not the carrier, and `Channel.send`/`recv` are the same: an awaiting operation is a
`Task.Async`, and one that cannot park (`Mutex.tryLock`, `Semaphore.tryAcquire`, `Channel.trySend`,
`Channel.tryRecv`) is an `IO` — the same split as `Join.resolve` against `Async.await`. None of them guards a
value or promises an order. The mutex is one permit and no guard (Lean has no drop hook that could release, so
`unlock` is explicit), it is not reentrant and carries no owner check, and the order in which waiters are
admitted is unspecified — §5's "no fairness or priority guarantee" governs here too. `Channel.new` refuses a
capacity of zero rather than handing back a channel that can serve no sender.

The mechanism is the task layer's own, on `Join` and `ctx.resume` — **not** an adapter over `Std.Sync`, and the
reason is the cancellation law stated above. An adapter hands a waiter what it asked for *irrevocably*:
`Std.Sync.Semaphore.release` resolves the waiter's promise (`Std/Sync/Semaphore.lean:76-87`) and
`Std.Sync.Channel.recv` dequeues the message into the task it returns (`Std/Sync/Channel.lean:542-546`). Our gate
is `Item.fire`, which skips a cancelled computation's step — but nothing can un-resolve a promise or re-enqueue a
dequeued message, so a waiter the runtime skips has already consumed the permit or the message. The law forbids
exactly that: a cancelled waiter is granted nothing and consumes nothing. Our mechanism satisfies it because a
wake is only a hint — the waiter acquires in its own step, and a skipped wake transfers nothing. *This is D14's
design, and it is built: `LeanIn/Task/Sync.lean`, and SC13 drives it at the public executable.*

**A task-local context is carried, not threaded.** `LeanIn/Task/Basic.lean` gives the layer a `Local` record —
a `requestId`, a `deadline` and a tracing `trace` — carried as a field of `Ctx` (`Ctx.local`), with two
operations: `Async.local`, a field read of the immutable `Ctx` a step already holds, and `Async.withLocal`,
which runs a computation under a value. An `Async.spawn` inside a `withLocal` builds the child's `Ctx` from the
parent's, so the child inherits the innermost enclosing value at its spawn site, and no signature between a
reader and its caller gains a parameter. The record is typed rather than a name-keyed store: a reader and a
writer agree by type rather than by convention, and the child takes one immutable copy at its spawn site rather
than a map behind a second lock. Nothing in the runtime reads these fields — the runtime schedules, and a
caller's log line or deadline check reads them. *This is D16's design, and it is built: `LeanIn/Task/Basic.lean`,
and SC15-O1 drives it at the public executable.* Its scoping is read as a one-carrier pair — inheritance by a
spawned child and non-inheritance by an unrelated computation — because the clause's second half ("and not from
a task on another carrier") needs a second carrier that does not exist yet: W8, and O2 below.

**A `JoinSet`-shaped set of handles is the task layer's own, and drains by awaiting.** `LeanIn/Task/Registry.lean`
is one `Std.Mutex` over a membership `List`, with `new`, `add`, `spawn`, `size`, `joinAll` and `drain`. Every
operation is a critical section over pure list code; the awaits happen *outside* the lock, on a snapshot the lock
has released, because running a continuation inside would enqueue — which takes the executor's lock — while
holding this one. The registry is **unbounded**: it holds handles, it does not meter admissions. The connection
limit stays the proved semaphore in `Runtime.serveBounded` (D15), so a second bound inside the registry would be
a second place the limit lives and would make `add` a parking operation, wrong for a drain path. `drain` takes
the whole membership in one critical section, clears the registry, and awaits each taken handle outside it; that
await is what makes its return mean the handlers finished. The registry holds handles, not **ownership**: dropping
it aborts nothing — Lean has no drop hook that could (W5) — and a handle it took is still awaitable by anyone else
holding it. `drain` awaits rather than cancels: cancelling what outlives a deadline is `Runtime.cancel`, issued by
whoever holds the clock. *This is D16's design, and it is built: `LeanIn/Task/Registry.lean`, its `joinAll`/`drain`
`drain` in `Net.lean`'s serving loops, and SC15 drives it at the public executable.*

**A handle is a narrowed capability, and the narrowing is the design.** `Runtime.handle (e : Sched.Executor α cap) : Handle α cap`
holds the executor and exposes exactly three operations: `Handle.spawn (h) (prio) (a) : IO (Task.Task α)`,
which builds the child's item — `Join.new`, `Cancel.new`, `Task.Item.stamp` — and routes it through
`Executor.spawnBase` (`.high`) or `Executor.submitBase` (`.normal`), the two placements D17 already fixed;
`Handle.stop (h) : IO Unit`, which is `Executor.stop`; and `Handle.metrics (h) : IO Metrics`. The executor is
a **private field with a private constructor**, so this is the type's surface rather than a convention: from
outside the module a caller can neither project the executor out of a `Handle`, build one, nor pattern-match
one apart, and so cannot reach a carrier-side operation through it. What it **withholds** is the point:
`Executor.work`, `Executor.park`, `Executor.tryTake`, `Executor.snapshot` and
every `Hooks` operation are carrier-side and are not reachable from a `Handle`, so a thread that is not a
carrier can originate work and ask the runtime to stop without being handed the whole executor. The claim
that makes its use off-carrier sound is `Handle.CriticalSections`: every shared cell those operations reach
is read and written inside that cell's own lock — the executor's `state`, its `cv` only inside a `state`
section, `Cancel`'s counter, `Join`'s own lock, and the counters — so their critical sections are
serializable against a carrier's and the executor's `State.Aligned`/`Scheduler.Live` invariants survive a
foreign-thread spawn. `Executor.submitBase`'s `cv.notifyOne` is issued inside the same `state` critical
section that records the work, which is the same lock the parking predicate is re-checked under, so a spawn
from a parked-against thread cannot be lost (P6 for this producer). This is an argument, not a theorem — it
needs the serializability lemma [`primitive-theory.md`](primitive-theory.md) §4 states as unproved — and it
is **not** a `Send` marker: it fixes one object by audit and checks nothing a caller shares with a thread.
The audit's one finding is a real defect: `Cancel.new`'s id allocator read and wrote an `IO.Ref` under no
lock, and a handle's spawn allocates a token off the carrier, so the allocator now does its read-modify-write
in one `Std.Mutex` critical section — a correction of D8's rule, not a new primitive. *This is D18's design,
and it is built: `LeanIn/Runtime/Basic.lean`, and SC17-O1 drives it at the public executable.*

**The counters are read through the model projection, so a counter cannot disagree with the model.** `Metrics`
is `ready : Nat`, `parked : Nat` and `carriers : Option (List CarrierCounters)`, where `CarrierCounters` is
`fired` and `busyNanos` per carrier. `ready` is `Pool.inFlight`, which `State.Aligned` proves equals
`Scheduler.work`, and `parked` is `Scheduler.parked`; `Executor.observe` reports the model projection's own two
fields — `work` and `parked` out of `Scheduler.toModel` — in one critical section that mutates nothing, enqueues
nothing and notifies nobody, so a read cannot perturb what it measures and cannot disagree with the model that
the scheduler's half of the refinement is stated over. `carriers` is `some` only for an executor built metered
(`Executor.newMetered`), and metering is opt-in so the default item path pays one `Bool` test and neither a
lock nor a clock read. Busy time is a duration in nanoseconds of whichever clock the driver was given, so
under a harness clock it is zero by construction (virtual time does not advance while work runs); it is
printed and never asserted, the `runUs` precedent. *This is D18's design, and it is built:
`LeanIn/Sched/Executor.lean`, `LeanIn/Runtime/Basic.lean`, and SC17-O1 reads `readyBefore`/`parkedBefore`/
`readyAfter`/`parkedAfter` across a thread boundary.*

**Time enters as a parameter, and the harness drives it rather than replacing the timer.** `Clock` is
`{ now : IO Nat, sleep : Std.Time.Millisecond.Offset → Task.Async Unit }`; `Runtime.sleep` and
`Runtime.withTimeout` take one, and `Clock.live hooks` is today's exact composition — `IO.monoNanosNow` for
the reading and the libuv timer behind W1's seam for the wait — so the production path is the same code it
was, reached through a record instead of directly. `HarnessClock` is the second implementation: a virtual
`now` and a sorted list of timers under its own mutex, with `advance : IO Bool` moving `now` to the earliest
deadline and firing that timer; its `sleep d` schedules at `now + d` and registers nothing with libuv, so no
live clock is read on a harness run. `Runtime.runVirtual (hc) (e) (a)` is `Runtime.runWith (e) (now := hc.now)
(idle := fun _ => hc.advance)` — the general driver with the harness's reading for the metered path and one
advance per idle round — so it parks exactly as `blockOn` does when nothing can be advanced to, which keeps
it composable with a live leaf or another thread's delivery. No production primitive is added: `Clock.live`
composes two things already on the register, and `HarnessClock` calls no clock at all. The harness clock is
exercised by SC17-O3, at a stated instant rather than by waiting; the serving loops build `Clock.live hooks`
locally, so a harness-driven drain is not offered. *This is D18's design, and it is built:
`LeanIn/Runtime/Clock.lean`, `LeanIn/Runtime/Time.lean`, and SC17-O3 drives it at the public executable.*

______________________________________________________________________

## 5. Deliberately absent

Each of these is a decision, not an oversight:

- **No heterogeneous `select`, and no guarantee about which ready handle wins.** `select`, `join` and `race`
  are now in §4 — the first-ready operation the layer needed, its all-of companion, and the runtime combinator
  that cancels the losers. What remains absent is generality and any ordering promise. `select` is over a
  homogeneous list, not the `Sum`-nested branches a `select!` macro expands to, so an arity-indexed or
  heterogeneous shape is not offered. And when several handles are ready it promises no fairness: it returns the
  first handle to *become* ready as it observed it, with list order breaking ties only among handles already
  resolved at the call — a rule about a race already run, not a claim about one to come. The timer's own
  handle — the deadline arm a request races against — is now *expressible*: the clock of §4 plus `Runtime.spawn`
  and `select` let a request race a timer's handle, and SC17-O3 decides one at a stated instant. What is still
  absent is the *policy* arm — a `Registry` that cancels what outlives a deadline, and the drain-liveness
  argument D16 deferred — which is D18's recorded open item.
- **No bare `wait`.** Only `awaitUntil`-shaped operations, because A4 permits spurious wakeups. A
  `Condvar.wait` without a predicate should be unrepresentable in `leanin`'s API.
- **No fairness or priority guarantee.** A1 gives none and A6 gives none. Nothing in the interface may
  read as promising that a task *will* run, only that it is queued. This governs §4's sync primitives too:
  a mutex's or semaphore's waiter order is unspecified, and a channel serves its queue FIFO and its waiters
  in no promised order. `Runtime.spawn`'s priority argument is not an exception: it selects a *placement
  lane* — the owner-local LIFO slot or the FIFO run queue — and promises nothing about when the task runs.
  It is honoured by the implementation and promised by no document; "high" is not a total order, and two
  `.high` spawns displace each other through the slot's ordinary overflow rule.
- **No atomics.** Not exposed (D4, D7).
- **No `Send`/`Sync`.** Lean has none; O2 in [`decisions.md`](decisions.md) is unresolved. Until it
  closes, the interface cannot be frozen — this is the one thing that blocks it. The task-local
  context is gated on the same item: it is per-computation and tested on one carrier, and the
  cross-carrier half of its inheritance law is W8's (D16). The `Handle` of §4 is not an exception: it
  is a narrowed capability fixing one object by audit, argued rather than proved, and it neither checks
  nor restricts what a caller shares with a thread — so it does not close O2 and must not read as if it
  did.
- **No consistent counter snapshot, and no pacing guarantee for an external signal.** A `Metrics` read
  takes two short critical sections — `Executor.observe` for `ready`/`parked`, the counters lock for the
  per-carrier list — and copies scalars, so it is not a single-instant image of the whole executor, only
  what each critical section saw. And a registered signal is delivered by the OS: nothing here promises
  *when* a `kill` reaches the handler, only the order of what the handler then did (SC10, SC17).
- **No `shutdown` and no abort-all on the registry.** `LeanIn/Task/Registry.lean`'s `drain` awaits what it
  holds; it does not cancel. Cancelling what outlives a deadline is `Runtime.cancel`, already public and
  issued by whoever holds the clock, and the registry's contribution is only that it then drains. An
  operation that cancels the membership itself — a `Registry.shutdown`/`abortAll` — is deliberately absent:
  its cancellation half is that same `Runtime.cancel`, and testing "outlives the deadline" needs a clock it
  can advance, which the harness clock of §4 now provides (W13); the cancel arm itself is still absent, so
  this is D18's open item rather than a missing instrument.
- **No `LocalSet`, `block_in_place`, `block_on`-variants, or runtime-flavour enum** in v1. One flavour
  (single-carrier, D2), shaped on `LocalRuntime`.

______________________________________________________________________

## 6. What refinement means here

For each operation, the concurrent implementation must be observationally indistinguishable from the
model under some interleaving:

```
Impl.push  ⊑ Model.push        Impl.pop  ⊑ Model.pop       Impl.steal ⊑ Model.steal
Impl.spawn ⊑ Model.spawn       Impl.await ⊑ Model.await
```

and the scheduler's three obligations (no lost wakeup, no lost work, bounded work per tick) are
theorems about the model, discharged in `Impl` by the serializability argument of
[`primitive-theory.md`](primitive-theory.md) §4.

The model is **executable**, so the first tests are against it — small queues, small schedules,
enumerated interleavings — before any thread exists. That is the fastest available feedback, and it is
why the model is not a formality.

For the **service** — the socket accept loop plus one connection body, both in
[`LeanIn/Runtime/Net.lean`](../LeanIn/Runtime/Net.lean) — the model is
[`LeanIn/Model/Service.lean`](../LeanIn/Model/Service.lean), and each obligation is paired with the
declaration it refines and the executor evidence it has:

| Obligation | Model declaration | Executor counterpart |
|---|---|---|
| every accepted connection is either completed or closed, never silently dropped | `Service.NoDrop` — `live ++ completed ++ closed` is `Nodup` and has length `admitted` | the connection record's `completed ∪ closed = accepted` as an id multiset, read by SC14-O1 |
| the number of live connections never exceeds its bound | `Service.Bounded` — `live.length ≤ bound` | `Runtime.serveBounded`'s permit, and the record's `liveHighWater ≤ bound` with the affirmative control `liveHighWater = bound`, read by SC14-O2 |
| every request gets a response or an error within its deadline — *the answer happens* | `Service.RequestsResolved` — `responded + errored + pending.length = requests` — and `Service.PendingWithinLive` — `∀ i ∈ pending, i ∈ live` | the record's `responded ∪ errored = requests` disjointly, read by SC14-O3 |
| … *the answer is observed to happen* | — | SC14-O3's clock-free event order: `deadlineFired = yes` alongside the population of both `responded` and `errored` |

The obligations are proved over the model's reachable states: `Service.Reachable` with
`reachable_invariants` and its per-obligation projections `reachable_noDrop`, `reachable_bounded`,
`reachable_requests` and `reachable_pendingWithinLive`, the whole guarded by `Service.WF`, and a
breaking-control per invariant (`abandon_breaks_noDrop`, `acceptBeyondBound_breaks_bounded`,
`closeDropping_breaks_requests`). `Service.NoDrop` is the partition "every admitted connection appears
exactly once, in exactly one of `live`/`completed`/`closed`"; `Service.Bounded` is the admission bound
the loop's permit enforces; and obligation 3's *safety* half is what is proved, while its *liveness*
half — that a pending request *eventually* reaches its deadline — is not provable from A1–A7 and is not
claimed ([`primitive-theory.md`](primitive-theory.md) §6).

The operation correspondence is argued per operation, the shape of `Impl.push ⊑ Model.push` above:

| Model | Executor | What is argued |
|---|---|---|
| `Service.accept` | the loop's `tryAcquire`-then-`Listener.accept` (`Runtime.serveBounded`) | the loop admits only while a permit is held, so `live.length ≤ bound − permits`, with equality only when no accept is in flight and no body is in its release gap — a permit is held *during* the accept, before a connection exists for it, and a body holds its permit past its end event — and `Service.Bounded` follows; the loop assigns no id, so an admission ordinal is never a connection identity |
| `Service.request` | the body's `recv` of the staged id | each admission begins at most one request at a time, because the body is serial |
| `Service.respond` | the body's echo | a returned echo is exactly one `responded` |
| `Service.deadline` | `withTimeout` returning `none` (`LeanIn/Runtime/Time.lean`) | the deadline transition's executor witness; that the timer *fires* is `Std.Async`'s leaf, not proved here |
| `Service.complete` | the body's EOF return `.ok` | a connection that returns normally is `completed` |
| `Service.close` | the body's `.error` (socket failure, a staged failure, EOF before a request) | a connection that terminates without completing is `closed`, and any request it owed is `errored` — `Service.close`'s `pending → errored` |

This correspondence is **argued, not proved**: the refinement theorem `Impl.op ⊑ Model.op` for the
service's operations is P8's open gap ([`proof-strategy.md`](proof-strategy.md) §3), and the link
between the two columns is the serializability argument of
[`primitive-theory.md`](primitive-theory.md) §4, which is itself an argument rather than a theorem.
SC14 is the executable correspondence test; its clause SC14-O2 is read from the executor's own
`begin`/`end` annotations, and it is deliberately an order-independent set/inequality detector rather
than the pairwise-oracle idiom of SC3, because the live server's interleaving is not deterministic. The
decision, its argued correspondence and the two limits it carries are recorded in
[`decisions.md`](decisions.md) D15. Both limits are stated plainly there: SC14 exercises only the
success-path permit release, so the wrapper's error branch is total **by construction** rather than
observed; and a cancelled body's release step is skipped by `Item.fire`, so a permit can leak — that
loses admission **liveness** (a service that cancels many bodies can slowly stop admitting), and it does
not breach `Service.Bounded`, since a leaked permit can only reduce admissions.
