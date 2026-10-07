# What scheduler does Lean actually use?

Answered from source, not from documentation. Source of truth: `Vendor/lean4`, tag
`v4.35.0-rc3`, commit `470d5ce1400764999581fd26d5d72b00d990b0f4` — **the same commit reported by
`lean --version` for the installed toolchain**, so this is the exact runtime that runs our builds.

The surprise is that there is no separate scheduler file. `src/runtime/object.cpp` (3 023 lines)
holds the task object, the task manager **and** the scheduling policy. There is no `task.cpp`.

---

## 1. The answer in one paragraph

There is exactly one scheduler. It is a **global, mutex-protected array of nine FIFO deques, one per
priority (0–8)**, drained by a pool of worker threads sized from `LEAN_NUM_THREADS` or the core
count. **Strict priority order, FIFO within a priority, no per-worker queues, no work stealing, no
LIFO slot, no fairness.** Priority above 8 means "one dedicated OS thread per task". Priority
`UINT_MAX` (`LEAN_SYNC_PRIO`) means "run inline on the submitting thread". Blocking a pooled task
occupies a worker thread; `Task.get` called from a pooled task *raises the pool cap* to compensate.
Separately, **one** dedicated thread runs a libuv event loop, and that is what timers and non-blocking
I/O use — the two mechanisms share nothing.

---

## 2. The data structure

`object.cpp:753–765`:

```cpp
class task_manager {
    mutex                                          m_mutex;
    std::vector<std::unique_ptr<lthread>>          m_std_workers;
    unsigned                                       m_idle_std_workers{0};
    unsigned                                       m_max_std_workers{0};
    unsigned                                       m_num_dedicated_workers{0};
    std::deque<lean_task_object *>                 m_queues[LEAN_MAX_PRIO+1];
    unsigned                                       m_queues_size{0};
    unsigned                                       m_max_prio{0};
    condition_variable                             m_queue_cv;
    condition_variable                             m_task_finished_cv;
    condition_variable                             m_dedicated_finished_cv;
    bool                                           m_shutting_down{false};
```

with `LEAN_MAX_PRIO 8` and `LEAN_SYNC_PRIO std::numeric_limits<unsigned>::max()`
(`object.cpp:71–72`).

That is the whole scheduler state. Nine `std::deque`s, one mutex, three condition variables, three
counters. **There is no per-worker run queue** — the "queues" are shared by every worker, and every
enqueue, dequeue and wakeup passes through `m_mutex`.

## 3. The policy

`dequeue()` (`object.cpp:767–782`):

```cpp
lean_task_object * dequeue() {
    std::deque<lean_task_object *> & q = m_queues[m_max_prio];
    lean_task_object * result = q.front();
    q.pop_front();
    m_queues_size--;
    if (q.empty()) {
        while (m_max_prio > 0) { --m_max_prio; if (!m_queues[m_max_prio].empty()) break; }
    }
    return result;
}
```

- `m_max_prio` is a cached high-water mark; on emptying a level it scans down. So `dequeue` is the
  highest non-empty priority, and within it **`front()` — FIFO**.
- There is no victim, no steal attempt, no retry, no locality. The whole policy is "highest priority,
  oldest first".

`enqueue_core` (`object.cpp:784–804`) decides where a task goes:

```cpp
if (prio == LEAN_SYNC_PRIO) { run_task(lock, t); return; }        // run inline, on this thread
if (prio >  LEAN_MAX_PRIO)  { spawn_dedicated_worker(t); return; } // one OS thread, just for this task
if (prio >  m_max_prio) m_max_prio = prio;
m_queues[prio].push_back(t);
m_queues_size++;
if (!m_idle_std_workers && m_std_workers.size() < m_max_std_workers) spawn_worker();
else m_queue_cv.notify_one();
```

Three destinations, and they explain the three priority bands in the Lean API
(`Task.Priority.default = 0`, `max = 8`, `dedicated = 9`).

## 4. The worker pool

- **Size**: `get_lean_num_threads()` (`object.cpp:1106–1112`) reads `LEAN_NUM_THREADS`, else
  `hardware_concurrency()` → `std::thread::hardware_concurrency()` (`thread.h:53`). Passed to
  `task_manager(max_std_workers)` via `lean_init_task_manager_using` (`object.cpp:1097–1104`).
  **If the count is 0, no task manager is constructed at all.**
- **Worker loop** (`spawn_worker`, `object.cpp:826–865`): wait on `m_queue_cv` while the queue is
  empty or while the pool is at its cap; `dequeue()`; `run_task(...)`; `reset_heartbeat()`.
- **Growth is demand-driven and lazy** — a new worker spawns only when *no* worker is idle at the
  moment of the enqueue. A burst of brief tasks can therefore leave the pool under-populated, which
  is visible in the measurements below (at `LEAN_NUM_THREADS=2` the thread-identity probe saw one
  thread for a burst of 64 trivial tasks, while the timing probe proves two were working).
- `run_task` (`object.cpp:880–920`) applies the closure with `lean_apply_1(c, box(0))` **with the
  mutex released**, then re-acquires it. A closure returning `nullptr` is a `bind` continuation: it
  registered itself as a dependency of a nested task instead of finishing (`add_dep`,
  `object.cpp:1004–1018`). `handle_finished` (`933–950`) walks the dependent list and re-enqueues.

## 5. Escape hatches (the two ways out of the pool)

| Condition | Behaviour | Anchor |
|---|---|---|
| `prio > LEAN_MAX_PRIO` (9+) | a **dedicated OS thread per task**; bypasses the pool entirely | `object.cpp:792–794`, `868–878` |
| `prio == LEAN_SYNC_PRIO` (`UINT_MAX`) | **run inline** on the submitting thread; also what `Task.map … (sync := true)` uses | `object.cpp:788–791`, `1211`, `1273` |
| `Task.get` from a pooled task | **raises `m_max_std_workers` by 1** while it waits, spawning a worker if none is idle, so the blocked worker is replaced | `object.cpp:1020–1042` |
| `Task.get` from a `sync := true` task | `lean_panic("Task.get called from a (sync := true) task")` | `object.cpp:1028–1030` |

The third row is why the documented "no more workers than cores" is only a *steady-state* claim: the
pool is explicitly grown around a blocking `Task.get`.

## 6. The reactor is a separate thread, and it is not the pool

`libuv.cpp:19–27`:

```cpp
extern "C" void initialize_libuv() {
    initialize_libuv_timer();
    initialize_libuv_tcp_socket();
    initialize_libuv_udp_socket();
    initialize_libuv_signal();
    initialize_libuv_loop();
    lthread([]() { event_loop_run_loop(&global_ev); });   // one dedicated thread, for all I/O
}
```

`event_loop_run_loop` (`uv/event_loop.cpp:85–100`) loops on `uv_run(loop, UV_RUN_ONCE)`.
Cross-thread access is a hand-off: `event_loop_lock` (`69–76`) try-locks and, on failure, sends a
`uv_async_t` interrupt that makes the loop call `uv_stop` and yield the mutex.

So the runtime has **two independent scheduling mechanisms**: the task pool, and one libuv loop
thread. Waiting on a timer or a socket costs *no* pool worker — which is exactly what the
measurements show.

## 7. `IO.sleep` is a debug helper, and its Lean definition is a lie

This one is worth reading in full because it is the sharpest possible illustration of
`docs/proof-strategy.md`'s Gap A.

```lean
-- Init/System/IO.lean:433
-- TODO: add a proper primitive for IO.sleep
opaque sleep (ms : UInt32) : BaseIO Unit :=
  fun s => dbgSleep ms fun _ => .mk () s

-- Init/Util.lean:41-42
@[extern "lean_dbg_sleep"]
def dbgSleep {α : Type u} (ms : UInt32) (f : Unit → α) : α := f ()   -- ignores `ms` entirely
```

```cpp
// object.cpp:2881-2885
extern "C" LEAN_EXPORT object * lean_dbg_sleep(uint32 ms, obj_arg fn) {
    chrono::milliseconds c(ms);
    this_thread::sleep_for(c);
    return lean_apply_1(fn, lean_box(0));
}
```

So `IO.sleep` is a genuine blocking OS sleep **on a pool worker**, reached through a *debug* entry
point, with a Lean-level body that returns immediately. Any theorem about `IO.sleep` would be a
theorem about `f ()`. This is not a hypothetical about the TCB; it is the current state of the
standard library.

(For contrast, `Array.push`'s extern carries a *correct* pure body. That difference is the whole of
Gap A.)

## 8. Measured, and it matches the source exactly

The pool size is a dial, and `IO.sleep` scales as `ceil(64/N) × 100 ms` while `Async.sleep` is flat:

| `LEAN_NUM_THREADS` | distinct threads seen | 64 × `IO.sleep 100` | 64 × `Async.sleep 100` | `Async.async` 2 × `IO.sleep 200` |
|---|---|---|---|---|
| 1 | 1 | **6406 ms** | 102 ms | 401 ms |
| 2 | 1 (burst probe) | **3203 ms** | 102 ms | 200 ms |
| 4 | 4 | **1602 ms** | 101 ms | 201 ms |
| 8 (default) | 7–8 | **801 ms** | 102 ms | 200 ms |

Readings:

1. **`IO.sleep` scales exactly as `ceil(64/N)`** — 6406 / 3203 / 1602 / 801. One blocked worker per
   sleeping task, confirmed four times over. Blocking work occupies the pool.
2. **`Async.sleep` is flat — 102 ms even at `LEAN_NUM_THREADS=1`** — because the libuv loop thread
   services the timers and consumes no pool worker. The reactor genuinely works.
3. **The thread-identity probe under-reports for bursty work** (1 thread observed at
   `LEAN_NUM_THREADS=2`, while the timing proves 2-way parallelism). The timing probe is the reliable
   instrument for pool width; the TID probe measures concurrency actually exercised by short tasks.
   This is a methodological correction to `docs/evidence.md`.

---

## 9. What this means for `leanin`

The findings sharpen the project rather than changing it, but they do change *which* questions are
open — and the honest answer to "do we have a viable plan" is **not yet**, because three of these
constrain the design more than the previous framing assumed.

**a. There is no runtime object to replace.** The scheduler is a global singleton
(`static task_manager * g_task_manager`, `object.cpp:1095`), constructed once at startup and
destroyed at exit. There is no `Runtime`, no handle, no way to instantiate a second one. So a
`leanin` scheduler cannot be "wired in" — it is either:

- **(i) a patch to `object.cpp`** (and therefore to the toolchain we build against), or
- **(ii) a parallel scheduler that owns its own OS threads and uses `Task` only for leaf work**, or
- **(iii) a foreign function + `@[extern]` swap for `lean_task_*`**, which needs a Lean-side model to
  be sound at all.

This is a much more concrete version of M0's D1, and it should be decided before the roadmap is
trustworthy.

**b. The contention story is real and easy to state.** Every spawn, dequeue and wakeup takes one
global mutex, and every worker contends on the same nine deques. That is precisely what Tokio's
per-worker queues plus stealing exist to avoid, and it means the work-stealing target is not
hypothetical: it is the standard fix for the structure we just read. **This is now the strongest
argument for building it.**

**c. The blocking problem is worse than "IO.sleep blocks".** It is implemented through
`lean_dbg_sleep` — a debug utility — and the Lean definition doesn't even describe the behaviour. Any
blocking FFI on a pooled task silently costs a worker. A blocking pool (the cheapest large win in the
plan) is still the right first move, and it no longer depends on the scheduler work at all.

**d. Strict priority is a fairness bug waiting to be named.** Nine FIFO deques with no aging means a
sustained stream at priority 8 starves priority 0 indefinitely. `Task.Priority` is documented as
"higher priority will always be scheduled before lower", so this is intended — but it means "fairness"
is a property the current scheduler does *not* have, and any fairness theorem for `leanin` is a
genuine addition rather than a transcription.

**e. `Async` can be re-based without touching I/O.** Because the reactor is a separate thread and
`await` never blocks a pool worker, the async surface (`Std.Async`) is largely independent of the
scheduling policy. That is good news: a `leanin` scheduler could serve `Std.Async` with the libuv loop
untouched.

**f. `LEAN_NUM_THREADS=0` disables the task manager entirely** — a configuration worth probing before
relying on any assumption about `Task` behaviour.

## 10. Open questions this raises

1. Does anything in-tree (`Lean.Server`, `Lake`, `Lean.Language`) depend on the singleton's exact
   behaviour — priority ordering, or the `Task.get` pool-growth hack — such that replacing it would
   break them?
2. Is the demand-driven worker spawn a *deliberate* throttle or an accident? The comment at
   `object.cpp:849–857` discusses throttling after `task_get` decreased the cap, which suggests it is
   deliberate, but the under-spawn for bursts looks unintended.
3. What happens to `Task.get`'s cap-bump under a work-stealing scheduler — is "blocked worker is
   replaced" even a meaningful idea when stealing exists?
4. Which of (i)/(ii)/(iii) in §9a does the toolchain permit? (ii) is the only one that needs no
   toolchain patch, and (i) is the only one that makes the whole async layer provably ours.
