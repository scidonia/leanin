# Proof strategy

This is the part of the plan that decides whether the project is worth doing at all. The question is
not "can we write a work-stealing scheduler in Lean" — that is ordinary engineering. It is **"what
can we actually prove, about what, with which tool, and what has to stay assumed."**

______________________________________________________________________

## 1. The three nested gaps

Proving anything about a scheduler here means crossing three gaps, and they are different in kind.

**Gap A — Lean has no semantics for concurrency, of any kind.** Not machine-checked, not
pen-and-paper, not even a manual-level operational semantics. What exists is a *typing discipline* for
effect ordering: `IO.RealWorld` is `opaque`, `BaseIO α := ST IO.RealWorld α`, and the manual says
effects are "abstractly described in Lean's logic" with "the Lean runtime system … responsible for
actually carrying out the described effects". There is no transition relation anywhere.

The decisive evidence is the shape of the `@[extern]` declarations, and it is worth reading directly,
because it is easy to assume the primitives have *some* model:

```lean
-- Init/Core.lean ~684
@[noinline, extern "lean_task_spawn"]
protected def Task.spawn (fn : Unit → α) (prio := Priority.default) : Task α := ⟨fn ()⟩
protected def Task.map  (f : α → β) (x : Task α) : Task β := ⟨f x.get⟩
-- Init/System/ST.lean
@[extern "lean_st_ref_get"] opaque Ref.get (r : Ref s α) : ST s α := inhabitedFromRef r
```

Those "pure bodies" are **not models of anything**: `Task.spawn`'s body runs the computation
*eagerly on the current thread*, which is the opposite of spawning; `Ref.get`'s body returns an
**arbitrary inhabitant** (`inhabitedFromRef r := pure default`). There is no model of parallelism and
none of mutable state.

This matters because Lean *does* have a first-class pattern for reasoning about a pure model while
trusting a native implementation, and concurrency is the one place it does not apply. `Array` is
defined as `structure Array (a) where toList : List a`, and its externs carry **correct** pure bodies
(`@[extern "lean_array_push"] def Array.push a v := { toList := List.concat a.toList v }`), so every
theorem about `Array` is a theorem about `List` and the C++ routine is merely trusted. `String`,
`ByteArray` and `UInt` follow the same discipline, and `@[implemented_by]` provides the
verified-optimisation variant. **For `Task`, `IO`, `Promise` and `ST.Ref` there is no correct pure body
to prove against** — which is precisely why "prove the scheduler" cannot, today, mean "prove the Lean
program".

`Std.WP` does not close this: it has instances for `Id`, `Option`, `Except`, `EStateM`, `StateT`,
`ReaderT`, `OptionT`, `ExceptT` — and **none for `IO`, `BaseIO`, `EIO`, `Task`, `Promise`, `ST` or
`ST.Ref`**. `BaseIO` has a *trivial* `MonadAttach` via `ST`, which is inert for reasoning: any
`CanReturn` instance we supply must be a real relation, not `MonadAttach.trivial`.

So there is nothing to prove the running program *about* — which converts Gap A from a nuisance into
a design decision (see §4, Layer 3).

The clearest example is in the standard library itself rather than in our own code, so it is worth
quoting: `IO.sleep`'s Lean definition is `fun s => dbgSleep ms fun _ => .mk () s`, its extern is
`lean_dbg_sleep`, and `dbgSleep`'s body is `f ()` — **it ignores the duration**. The C++ side really
does `this_thread::sleep_for(...)`. So the Lean term for a blocking sleep denotes a no-op, and a
theorem proved about `IO.sleep` would be a theorem about `f ()`. See
[`docs/lean-scheduler.md`](lean-scheduler.md) §7 for the full quotation.

**Gap B — concurrent separation logic in Lean is one month old.** `iris-lean`
(`leanprover-community/iris-lean`) is real, actively maintained (last commit 2026-10-06), ports the
complete non-experimental core of Iris, >80% of HeapLang, the proof mode, atomic triples, invariants
and later credits, and is described in "Iris in Lean" (arXiv:2609.24252) **[S]**. What it is *not*:
it is **sequentially consistent only** (no iRC11/Cosmo-style weak-memory instance), it has **no
work/span credits** (Parcas is Rocq-only), it restricts OFEs to Leibniz, and it has no Actris or
Simuliris **[S]**. Notably it *does* ship time receipts
(`Iris/Iris/Algebra/Lib/TimeReceipts.lean`) — the machinery for *amortized* reasoning — which is
exactly what a scheduler's cost argument needs.

**Gap C — scheduling theory does not exist in any proof assistant.** Not "not in Lean" — not
anywhere. There is no formalized Graham bound, no Brent theorem, no DAG makespan, no list
scheduling, no work-stealing bound, no parallel cost model **[S]**. Mathlib has `SimpleGraph.Walk`,
acyclicity and trees, and that is the whole of the reusable substrate. The Blumofe–Leiserson
randomized bound additionally needs balls-and-bins concentration that Mathlib does not have (Markov's
inequality is present; Chernoff/Hoeffding-style tails are not) **[S]**.

Gap C is the good news and the bad news. Bad: we build it. Good: **it is genuinely new, it is
mathematics rather than systems engineering, and it is the least risky thing in the project** — a
paper-and-Lean development of the work-stealing bound is a result on its own, independent of whether
the runtime ever lands.

______________________________________________________________________

## 2. The TCB, stated plainly

If we prove the scheduler in Lean, then the trusted computing base is:

| Trusted | Why | Can it shrink? |
|---|---|---|
| Lean kernel + `iris-lean` soundness | as with any Lean proof | no (and no need) |
| The **deque's atomics** — whichever C++/FFI primitives the implementation really calls | Iris reasoning is *about* a model of these; the model↔machine step is a leap | partially: keep the atomic set tiny and enumerate it |
| The **thread creation/parking syscalls** (pthreads, `futex`, `eventfd`) | the OS scheduler is outside every proof | no |
| **Lean's `Task`/`Promise`** if `leanin` is built *on top of* them — concretely `lean_task_spawn`, `lean_task_map`, `lean_task_bind`, `lean_task_get_own`, `lean_io_wait`, `lean_io_wait_any`, `lean_io_cancel`, `lean_io_get_task_state`, `lean_io_promise_new/resolve/result_opt`, `lean_option_get_or_block` | they are the substrate we cannot replace, and they have **no semantics** (Gap A) | partially: use as few as possible, or replace with our own |
| **The refinement from the proven model to the running Lean code** | unless the proven code *is* the running code | this is the hard one — see §4 |

The honest framing: **the proof is about a model of the scheduler, and the model is a design decision
that we control.** The project's central architectural question is therefore not "what do we prove"
but **"how thin can we make the layer between the proven model and the running code."** That is why
milestone 0 below is a decision about the *substrate*, not an implementation.

There is a real precedent for the shape we need. `@[extern]`-over-a-correct-pure-body is Lean's own
first-class practice (`Array`, `String`, `ByteArray`, `UInt` — see Gap A), and the cross-language
precedent for applying it to a *concurrent runtime* is Cosmo/Parabs over OCaml 5: prove a model of a
runtime you control, keep the C runtime as the trusted implementation, and prove the model against the
runtime's **published** semantics. The difference is that OCaml 5 publishes an operational semantics
and Lean does not — so **we would be authoring the model, not adopting one.** That is an extension of
an established Lean practice rather than an exotic concession, but it is genuine work and it belongs
in the plan rather than in a footnote. The alternative is to accept exactly the TCB that seL4
(Isabelle/HOL) and CertiKOS (Coq) accept for their verified schedulers and say so — noting that those
projects verify the actual C kernel, which Lean cannot do for its C++ task runtime.

______________________________________________________________________

## 3. The property ladder

Stated so that each rung is independently meaningful and independently provable.

| # | Property | Informal statement | Where it lives | Instrument |
|---|---|---|---|---|
| **P0** | Deque linearizability | the Chase–Lev/ABP deque is a linearizable deque: `push`/`pop`/`steal` behave as a sequential deque | concurrent data structure | `iris-lean` |
| **P1** | Steal safety | a pushed task is taken **at most once**; only pushed tasks are taken | deque + scheduler | `iris-lean` (invariant) |
| **P2** | Completion | with finitely many pushes, every pushed task is eventually taken or stolen exactly once, if stealing continues | scheduler loop | `iris-lean` + liveness/obligations |
| **P3** | Greedy bound | any greedy *P*-processor schedule satisfies `T_P ≤ T₁/P + T_∞` (Brent/Graham; BL Theorem 1) | pure model | **Mathlib-style, new** |
| **P4** | Work-stealing bound | BL Theorem 8: expected `T₁/P + O(T_∞)`, and w.h.p. `T₁/P + O(T_∞ + lg P + lg(1/ε))` | pure model | **new** (needs P3 + probability) |
| **P5** | Work-first / no idle worker with available work | if the local deque is non-empty the worker takes from it before stealing; the schedule is therefore greedy | pure model | new |
| **P6** | No lost wakeup | a task enqueued while all workers are parked results in a worker running | scheduler loop | `iris-lean` |
| **P7** | Cancellation correctness | a cancelled task never observes a post-cancellation step; cancellation is idempotent; a cancelled child cannot outlive its context | async layer | `iris-lean` + model |
| **P8** | Refinement | the running implementation is a refinement of the pure model of P3–P5 | the bridge | layered refinement |
| **P9** | Fairness (optional) | no ready task starves | scheduler loop | liveness logics |

The ladder is deliberately ordered so that **P3/P4/P5 are provable first and independently** — they
need no concurrency logic, no Iris, no runtime, and no semantics of Lean. They are pure mathematics
about DAGs and schedules.

______________________________________________________________________

## 4. Recommended proof architecture: three layers

```
  Layer 3  Lean runtime (Task, Promise, pthreads)        -- TCB, deliberately small
           ── refinement gap, documented and measured ──
  Layer 2  leanin scheduler over proven primitives        -- iris-lean: P0,P1,P2,P6,P7
           ── refinement ──
  Layer 1  pure scheduler model: DAG, schedule, stealing  -- Lean/Mathlib: P3,P4,P5
```

**Layer 1** — a pure, executable `Sched` model: tasks as DAG nodes with work/span, a `Schedule` as a
sequence of step assignments, `Greedy` and `workFirst` predicates, and a *deterministic* work-stealing
algorithm. P3, P5 and (with a probability theory layer) P4 are theorems here. **This layer needs
nothing from `iris-lean` and nothing from the runtime**, which is why it goes first.

**Layer 2** — the concurrent implementation: deque, inject queue, park/unpark, the worker loop.
Proved in **`iris-lean`** against the abstract deque/scheduler spec with the standard Iris toolkit
(invariants, atomic triples, ghost state, later credits). P0, P1, P2, P6, P7 live here. This is where
we must decide **whether the code being proved is Lean code or a modelled language** — see §5.

**Layer 3** — the substrate, i.e. what we do about Gap A. Three stances; the choice is milestone 0.

- **(a) Hosted.** Build `leanin` workers as `Task.Priority.dedicated` threads (or raw pthreads via
  FFI) that own `leanin` queues; keep using `Task`/`Promise` for the async surface. **Cheap, ships
  fast, but adds Lean's unverified `Task`/`Promise` to the TCB.** The proof then covers the deque and
  the scheduling policy, not the substrate.
- **(b) Owned.** Implement the worker pool, parking and wakeup directly on a minimal set of FFI
  primitives (`pthread_create`, atomics, `futex`/`eventfd`-style parking), using `Task` only where
  unavoidable. **Expensive, but makes the TCB enumerable** — a short list of atomic primitives, each
  with a stated model, which is exactly what the Rocq/Iris precedent (Parabs over OCaml 5's Saturn
  deque) does.
- **(c) Modelled — and this one is not optional.** Write the pure model Lean is missing: correct,
  non-placeholder Lean definitions of the concurrency primitives we rely on, bound to the native code
  with `@[extern]`, exactly as `Array`, `String` and `ByteArray` are. Every proof then targets the
  model and the native implementation is trusted — Lean's own established discipline, applied to
  concurrency for the first time.

(a) and (b) decide *which* runtime is trusted. (c) decides whether the trusted thing can be **stated**
at all. Without (c), the choice between (a) and (b) buys a tested system rather than a proven one,
because there is no term for a theorem to be about.

`Std.WP` supplies the recipe for (c): its own documentation (`Std/WP/Basic.lean:35–38`, and the
worked example in `tests/elab/vcgenImp.lean`) carries a full **deep-embedding** — a command language
given an **omnisemantics** plus a `WP` instance — which is exactly the shape of "give a language a
semantics and a program logic, then prove in that language". So the concrete M0 question is *which
language*: a small concurrent language with an omnisemantics defined inside Lean, or `iris-lean`'s
HeapLang.

**(b) + (c) is the combination that yields a result worth publishing.** (a) is the one that ships in
weeks. The plan sequences (a) → (b) and does (c) alongside.

______________________________________________________________________

## 5. What is genuinely tricky, ranked

**T1 — Proving code that runs.** Iris reasons about a *modelled* language (HeapLang, or a Rust-like
calculus). Lean's `IO` has no semantics at all (Gap A, and the placeholder bodies make it worse than
"unproven": `Task.spawn`'s own pure body runs eagerly, `Ref.get`'s returns an arbitrary inhabitant).
`iris-lean`'s HeapLang is not Lean. So we must choose how the thing being proved relates to the thing
that runs:

1. **Model + `@[extern]`** (the `Array` discipline): write correct pure Lean definitions of the
   primitives we rely on, bind them to native code with `@[extern]`, prove against the model, keep the
   native code as TCB. Established Lean practice; requires authoring the model.
1. **`iris-lean`/HeapLang**: write the concurrent core in the modelled language, prove it there,
   port the result. Loses the connection to Lean's own code and adds a porting step.
1. **A new `Std.WP` instance** for our own concurrent language with an **omnisemantics** —
   `Std.WP` has the framework and a worked deep-embedding recipe (`tests/elab/vcgenImp.lean`) but no
   `IO` instance and no concurrency, so this is authoring work; it is also the path most aligned with
   where the Lean FRO is going (`Std.WP` is being actively developed — PR #15290 moved `vcgen` into
   `Std.WP.Tactic` in September 2026, and PR #14685 is a "vcgen separation logic demo").
1. **Prove the model, argue the refinement in prose**: the fallback, and honest as long as the
   argument is a first-class document with an executable correspondence test.

**This is the single hardest and least-precedented item in the project**, and it is not a scheduling
problem at all — it is a semantics problem. Mitigation: keep the concurrent core *small and boring* (a
deque, a few atomics, a park/unpark pair) so the bridge is short enough to argue by inspection; pick
(1) as the near-term default because it is Lean's own idiom; treat (3) as the research bet; and make
the bridge a deliverable rather than a paragraph.

**T2 — Liveness.** Safety proofs are Iris's home turf; *liveness* is not. "Every pushed task is
eventually taken" and "no lost wakeup" require obligation/fairness reasoning. The state of the art is
`Lawyer` (OOPSLA 2026) and wait-freedom verification (ECOOP 2026) — **both Rocq**, with no Lean
counterpart **[S]**. Expect this rung (P2, P6, P9) to be the last one reached and possibly the one
that forces a Rocq sub-proof.

**T3 — Weak memory.** All the interesting memory-model work says the deque is subtle: Lê et al.
(PPoPP'13) prove Chase–Lev correct on ARMv7 with fences that **C11 cannot express**; BWoS (OSDI'23)
report that **Tokio's work-stealing queue required a fix** and that a C11 translation of verified
ARMv7 Chase–Lev assembly had a bug; Parabs (PLDI'26) needed 'wise' and 'multiplexed' prophecy
variables to capture a *future-dependent linearization point* in the deque's `pop` failure case
**[S]**. `iris-lean` is **SC-only**, so a Lean proof of a genuinely weak-memory deque is out of reach
today. Two ways out, both must be stated as assumptions rather than glossed: (i) restrict to a
`seq_cst`-only implementation (simple, slower, and defensible — Lean's runtime already uses C++11
`seq_cst` for its own refcounts and task fields **[R]**), or (ii) axiomatize a weak-memory model in
Lean, which is a research project on its own.

**T4 — Cost and amortized reasoning.** The bound is about *time*, and nothing in Lean does work/span
credits. `iris-lean` ships time receipts (`TimeReceipts.lean`), which is the right family of
machinery, but the work/span-credit design is Parcas (ICFP 2026, Rocq) **[S]** and would need
reimplementing. Also: `iris-lean` lacks **generalized step indices**, which several Iris cost/step
constructions rely on.

**T5 — The randomized bound.** BL's expected-time theorem needs the *P-M recycling game* tail bound
(balls and bins, negative association). Mathlib has measure theory, `PMF`, Markov, and no
Chernoff/Hoeffding-class concentration **[S]**. Formulating and proving the recycling-game tail is a
self-contained Mathlib contribution and a genuine prerequisite for P4.

**T6 — The substrate is unpatchable.** Lean exposes no way to *substitute* `Task`'s scheduler and has
no `Task`-level waker. A `leanin` scheduler is therefore either a policy layer over `Task`'s
dedicated threads, or an independent runtime using raw FFI. Either way, waking a parked worker must be
built from `Promise`/`Condvar`/`Task.spawn` — and that construction is itself concurrent code needing
its own proof.

**T7 — Iris-Lean maturity risk.** Built against Lean 4.32 in the paper **[S]**; whether it builds
against our pinned 4.35.0-rc3 is **unverified**, and the API is moving (47 open issues, commits every
few days). Also missing: Actris, Simuliris, Actris-style session/protocol reasoning that would
naturally express a `select`/`Notify` protocol **[S]**.

______________________________________________________________________

## 6. What we will *not* prove

Stated up front so the plan's claims stay honest:

- **Not** the OS: pthreads, the kernel scheduler, `epoll`, or libuv.
- **Not** the Lean kernel or the compiler's correctness (`lean4lean` covers the kernel only, and has
  no runtime/threading model **[S]**).
- **Not** the C++ implementation of `Mutex`/`Condvar`/`Promise` — only a model of them.
- **Not**, initially, weak-memory correctness of the deque (T3).
- **Not** an end-to-end "Lean source is correct" theorem — the bridge (T1) will be an argued
  refinement with a written model↔implementation correspondence, not a chain of proofs, until such
  time as a concurrent `IO` semantics exists.

______________________________________________________________________

## 7. Instrument selection, per rung

| Rung | Prove with | Evidence it is red first |
|---|---|---|
| P3, P5 | Lean + (Mathlib if needed) | a `#eval` counterexample schedule, or a vacuity check on the definitions |
| P4 | Lean + probability (new) | explicit small-`P` computation of the bound |
| P0, P1, P6, P7 | `iris-lean` (HeapLang instance or a small custom language) | the standard Iris route: state the spec, watch it fail on a deliberately-broken implementation |
| P2, P9 | `iris-lean` later credits; **Rocq/Iris if Lean can't** | a schedule exhibiting starvation |
| P8 | layered refinement (technique borrowed from mCertiKOS-style work) | mismatch between model trace and implementation trace on a scripted run |
| anything not provable yet | **deterministic replay + stress** | a scripted interleaving that must reproduce |

The user's environment already has `~/.opam/rocq-9` with `rocq-prover 9.0.0`, `coq-iris 4.4.0`,
`rocq-iris dev 2026-06-04`, `rocq-iris-heap-lang`, `coq-stdpp 1.12.0`, `coq-itree 5.2.1` and
`coq-lsp` **[S]** — so the Rocq fallback is installed and ready, not aspirational. Use it for liveness
(T2) and weak memory (T3) if Lean cannot host them.
