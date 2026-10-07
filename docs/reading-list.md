# Reading list: proving concurrency facts about schedulers

Annotated, ordered by what it decides rather than by date. Each entry says **what it gives us** and
its **verification status** — because in this literature "proved" means four different things
(machine-checked / pen-and-paper proof / model-checked under a bound / tested), and blurring them is
how projects end up claiming more than they have.

Legend: **[V]** verified status stated explicitly below · ⚠️ = known gap or limitation we must plan
around.

---

## Part I — What a scheduler must be proven to do

**1. Blumofe & Leiserson, "Scheduling Multithreaded Computations by Work Stealing."**
J. ACM 46(5):720–748, 1999. DOI `10.1145/324133.324234` (preliminary: FOCS'94, `10.1109/SFCS.1994.365680`).
→ **The target theorem.** Every other item exists to support, generalise, or mechanize this one.
Model: a multithreaded computation is a DAG with continue/spawn/join edges; `T₁` = work, `T_∞` =
critical-path length; threads form a spawn tree, and their bounds hold for **fully strict**
computations (every join edge goes to the parent).
The results to aim at:
- **Theorem 1 (greedy/Brent–Graham):** for *any* greedy *P*-processor schedule, `T(X) ≤ T₁/P + T_∞`.
- **Theorem 8 (main):** the Work-Stealing Algorithm runs in expected `T₁/P + O(T_∞)`, and with
  probability ≥ 1−ε in `T₁/P + O(T_∞ + lg P + lg(1/ε))`.
- **Lemma 6:** w.h.p. `O(P·(T_∞ + lg(1/ε)))` steal attempts; expected `O(P·T_∞)`.
- **Theorem 7 (space):** ≤ `S₁·P` stack space.
- **Theorem 9 (communication):** expected `O(P·T_∞·n_d·S_max)` bytes.
The analysis rests on a **P-M recycling game** (balls-and-bins) with `E[D] ≤ M` and a high-probability
tail — that lemma is *the* probabilistic prerequisite for us.
⚠️ Beware the folklore: "work-first" and "selfish" are *later* framings (e.g. Rice COMP 522 lecture
notes), not BL's own vocabulary. Value: **[pen-and-paper proof, no mechanization]**.

**2. Brent, "The parallel evaluation of general arithmetic expressions."** J. ACM 21(2), 1974.
**Graham, "Bounds for certain multiprocessing anomalies."** Bell Sys. Tech. J. 45, 1966; and SIAM J.
Appl. Math. 17(2), 1969.
→ The `T_P ≤ T₁/P + T_∞` bound, and the list-scheduling `(2 − 1/P)·OPT` bound. **Neither has a
machine-checked formalization in any prover** (a deliberate negative result — see Part X). Value:
**[paper only]**. These are the first rungs to mechanize, and mechanizing them is *new work*.

**3. Arora, Blumofe & Plaxton, "Thread scheduling for multiprogrammed multiprocessors."** SPAA 1998.
→ The original fixed-size-array work-stealing deque with a tag field against ABA. Needed to
understand why Chase–Lev exists (it removes the tag). Value: **[paper only]**.

---

## Part II — The deque, and its proofs

**4. Chase & Lev, "Dynamic Circular Work-Stealing Deque."** SPAA 2005. DOI `10.1145/1073970.1073974`.
→ The deque Tokio and everyone else actually uses: `pushBottom`/`popBottom` (owner) and `steal`
(anyone), a cyclic array that doubles, `top` never decremented, and the single-element `popBottom`
race resolved by CAS on `top`.
⚠️ The SPAA'05 paper contains only an informal argument plus **Lemma 1** (a steal never returns an
entry from a non-live array). The linearizability proof was promised for an **unpublished full
version and should be treated as absent.** Value: **[informal + one lemma]**.

**5. Lê, Pop, Cohen & Zappa Nardelli, "Correct and Efficient Work-Stealing for Weak Memory Models."**
PPoPP 2013. DOI `10.1145/2442516.2442524`.
→ The first real **correctness proof** of Chase–Lev, on ARMv7. It *defines* the four properties a
work-stealing deque must satisfy — **reverse order, well-defined reads, uniqueness, existence** — and
proves them against the ARMv7 axiomatic model by showing every incorrect execution graph would
contain a cycle. It also gives a C11 implementation that is optimal (no fence removable) and shows
the ARMv7 version **cannot be expressed with C11 atomics** (the C11 mapping adds a redundant `dmb`
before each CAS and an `mfence` between the two reads in `steal`).
→ **This is the correctness spec to adopt**, and this four-property formulation is what our P0/P1
rungs should mirror. Value: **[pen-and-paper proof, rigorous, not mechanized]**.

**6. Choi, "Formal Verification of Chase-Lev Deque in Concurrent Separation Logic."**
arXiv:2309.03642, 2023 (thesis).
→ First machine-checked Chase–Lev: Coq + CSL, with a minimal TCB, an unbounded realistic
implementation, and **linearizability** as the spec, plus safe memory reclamation.
⚠️ Relaxed memory is explicitly future work. Value: **[machine-checked, SC, Coq]**.

**7. Allain & Scherer, "A Verified Parallel Scheduler for OCaml 5" (Parabs).** PLDI 2026.
DOI `10.1145/3808337`; artifact `github.com/clef-men/zoo` (branch `pldi26-artifact`).
→ **The single most relevant prior art in this list.** A *verified work-stealing task scheduler* for
OCaml 5's domain pool, in Iris/Zoo/Rocq: the Saturn Chase–Lev deque plus a bounded
(Moonpool/Taskflow-style) variant and an idealized infinite-array variant; ~2K lines OCaml vs
~26K lines Rocq; performance comparable to Domainslib.
→ Two transferable ideas we should steal: (i) their spec covers the **failure case of `pop`**, not
just success, and they argue (against the weaker spec of Jung et al. 2023) that this is *required* to
prove **scheduler completion** when queues drain; (ii) they identify a **"future-dependent
linearization point"** in `steal` and handle it with *wise* and *multiplexed* prophecy variables.
→ Read this first for architecture, last for porting (Rocq, not Lean). Value: **[machine-checked, SC,
Rocq/Iris]**.

**8. Wang et al., "BWoS: Formally Verified Block-based Work Stealing for Parallel Processing."**
OSDI 2023.
→ Verified + optimized a block-based work-stealing queue. ⚠️ Not a theorem-prover proof: it
**model-checks** C with GenMC under IMM/RC11 for memory safety, data-race freedom, "each element read
once", and loop termination, then uses VSync to place barriers optimally.
→ Read it for two warnings that matter to us: **Tokio's work-stealing queue needed a fix**, and a C11
translation of *verified ARMv7 Chase–Lev assembly* had a bug. Value: **[bounded model checking]**.

**9. van Kampen, "Formal Automated Verification of a Work-Stealing Deque."** 32nd Twente Student Conf.
on IT, 2020.
→ VerCors verification of Lace's split deque, functional correctness only, strongly-consistent memory
only; the author reports finding an *unsoundness artefact* (a false assertion that passed). Value:
**[include as a cautionary tale about tool trust, not as a source]**. ⚠️

---

## Part III — The logic: Iris, in Rocq and now in Lean

**10. "Iris in Lean."** de Medeiros, Stepanenko, Liu, Soeser, Leal, Tang, Vistrup, **Jung**,
**Carneiro**, Tassarotti, Sammler, Birkedal. arXiv:2609.24252, Sep 2026.
Lean port: `github.com/leanprover-community/iris-lean` (227★, Apache-2.0, last commit 2026-10-06 —
i.e. actively maintained in lockstep with Iris-Rocq).
→ **This is what makes the project viable in Lean at all.** Ports the complete non-experimental Iris
core: CMRA/resource algebras (`Auth`, `Frac`, `FracAuth`, `ExclAuth`, `MonoNat`, `Heap`, `UFrac`,
`LocalUpdates`, …), BI, the **proof mode**, the language-parametric program logic, **atomic triples**
(`ProgramLogic/Atomic.lean`, `BI/Lib/Atomic.lean`), **HeapLang** with full semantics/proof mode/
primitive+derived laws, later credits, and `IrisMath` (measure theory in the SProp-free base). A new
tactic **`Wander`** plays Diaframe's role; `ifix`/`icofix`/`iguarded`/`iinductive` supply fixed-points.
Benchmarked against Iris-Rocq; >80% of the HeapLang logic ported; built on Lean 4.32 in the paper.
⚠️ Gaps that bound what we can do: **sequentially consistent only** (no iRC11/Cosmo instance);
**no generalized step indices**; OFEs restricted to Leibniz; set-based BI quantifiers; no Actris, no
Simuliris, no work/span credits. `TimeReceipts.lean` *is* present.
⚠️ **Does it build against our pinned 4.35.0-rc3? [UNVERIFIED — milestone 0 must check.]**
Value: **[machine-checked, Lean 4]**. ⭐

**11. Iris project (Rocq/Coq).** `gitlab.mpi-sws.org/iris/iris`; docs & book at `iris-project.org`.
→ The reference logic, and the place to look for anything `iris-lean` lacks. Iris 4.5.0 (2026-03-05).
Value: **[machine-checked, Rocq]**. Fallback for rungs Lean cannot host.

**12. Mével, Jourdan & Pottier, "Cosmo: A Concurrent Separation Logic for Multicore OCaml."**
ICFP 2020. DOI `10.1145/3408978`; see also Mével's 2022 PhD thesis.
→ A CSL for **weak memory** (OCaml multicore), i.e. the weak-memory Iris instance we would need for
T3 and do not have in Lean. Value: **[machine-checked, Rocq]**.

**13. Moine, Westrick & Tassarotti, "A Separation Logic for Parallel Time Complexity with Work and
Span Credits" (Parcas).** ICFP 2026. DOI `10.1145/3828679`; `github.com/nobrakal/parcas`.
→ **The cost-reasoning design template.** Work credits + tagged span credits + transfer, i.e. exactly
the machinery needed to make the BL bound a *statement about the implementation* rather than a
statement about a DAG. Rocq-only, so adopting it in Lean is real work (T4). Value: **[machine-checked,
Rocq]**. ⭐

**14. "Lawyer: Modular Obligations-Based Liveness Reasoning."** OOPSLA 2026.
and **"Verifying Wait-Freedom for Concurrent Higher-Order Programs."** ECOOP 2026.
→ Liveness. This is the rung (P2/P6/P9) with the weakest Lean support; these are the current best
techniques. Value: **[machine-checked, Rocq]**. ⭐ (for T2)

**15. Moine, Westrick & Tassarotti, "All for One and One for All: Program Logics for Exploiting
Internal Determinism in Parallel Programs."** POPL 2026.
→ Relevant to `leanin`'s *deterministic test runtime*: proof techniques that exploit determinism
rather than reasoning around it. Value: **[machine-checked, Rocq]**.

---

## Part IV — Verified kernels and preemptive schedulers

The closest existing work to "verify a scheduler", and the source of the refinement methodology.
**Expect to read these for technique, not for a template to copy** — they verify kernels, not
userspace runtimes, and their concurrency model is a machine model rather than a program logic.

**33. CertiKOS / mCertiKOS.** Gu, Shao, Chen, Wu, Kim, Sjöberg, Costanzo, OSDI 2016, pp. 653–669
(`usenix.org/system/files/conference/osdi16/osdi16-gu.pdf`). Prequels: "Deep Specifications and
Certified Abstraction Layers", POPL 2015; "Certified Concurrent Abstraction Layers", PLDI 2018;
CACM 62(10), 2019.
→ **Coq.** Verified code is ClightX (a C variant) plus x86 assembly, linked with a thread-safe
CompCertX. The kernel mC2 is ~6,500 lines and runs on stock x86 multicore.
→ What is proven is **contextual refinement** — `∀P. [[K P]]_x86mc ⊑ [[P]]_mC2` — i.e. the
implementation behaves like its deep specification under *any* kernel/user context and *any* valid
interleaving. It is a **layered** proof: a certified abstraction layer is a triple `(L1; M; L2)` with
a mechanized proof that `M` over `L1` contextually refines `L2`; concurrency is tamed by
**environment contexts** `EC(L; A)`, which make each thread's reasoning local to a rely-style
description of the others rather than the whole machine.
→ ⚠️ **The fact we must internalise:** starvation-freedom of ticket and MCS locks (their Lemma 6) is
proved *only under an explicit fairness assumption on the hardware/OS scheduler*. **The scheduler's own
fairness is an assumption, not a theorem.** Our plan will be in the same position, and it should say
so in the same way.

**34. Real-Time CertiKOS / Virtual Timeline.** Liu, Rieg, Shao, Gu, Costanzo, Kim, Yoon, POPL 2020,
PACMPL 4(POPL) Art. 20, DOI `10.1145/3371088` (`flint.cs.yale.edu/certikos/publications/rtcertikos.html`).
See also "Compositional Virtual Timeline", OOPSLA 2022; Guo et al., CAV 2019.
→ **Coq.** Extends mCertiKOS with a **verified timer-interrupt handler and a verified preemptive
real-time scheduler**, proving temporal isolation and spatial isolation on top of functional
correctness. The "virtual timeline" is the abstraction that makes preemption tractable.
→ **The closest thing that exists to a verified preemptive scheduler.** Read it for how a *timing*
abstraction is designed so the scheduler can be reasoned about.

**35. Prosa** — `prosa.mpi-sws.org`, `github.com/PROSA-Project` (Coq). Machine-checked **schedulability
analysis** (response-time analysis) and the POET framework; see also "Verified RTA of FIFO
scheduling", RTSS 2022 (`people.mpi-sws.org/~kbedarka/rtss22.pdf`).
→ The analytics side: proving *timing properties of a policy*, rather than proving an implementation.
Relevant to P9 if fairness becomes a goal.

**36. seL4.** Klein et al., SOSP 2009, DOI `10.1145/1629575.1629596`; proofs in Isabelle/HOL, `l4v`.
→ Functional correctness of the kernel against its abstract specification. ⚠️ **The abstract
specification contains no scheduling policy** — so this famous proof says nothing about the
scheduler's fairness or optimality. SMP configurations are **unverified**; the mixed-criticality
scheduler (the part that is actually a scheduler) has RISC-V functional correctness done with
AArch64 ongoing. Assumptions are documented at `sel4.systems/Verification/assumptions.html`.
→ Read this to calibrate what "the kernel is verified" does and does not mean.

**37. Correction: "Komodo" is not a verified scheduler.** The citation "Komodo: A Verified Multi-Core
Scheduler" does not exist — not in the FLINT/CertiKOS publication list, not in the usual indexes.
The name belongs to Ferraiuolo, Baumann, Hawblitzel & Parno, **"Komodo: Using verification to
disentangle secure-enclave hardware from software"**, SOSP 2017, DOI `10.1145/3132747.3132782`,
artifact `github.com/microsoft/Komodo` — a verified ARM TrustZone enclave monitor in Vale, discharged
through Boogie/Z3. Verified enclave integrity and confidentiality; no multicore, no scheduling.
Recorded so the misattribution stops propagating.

**38. KIT.** Bevier, Hunt, Moore, Young, "An approach to systems verification", J. Automated Reasoning
5(4), 1989. An early kernel verified down to object code in Nqthm/ACL2 — single-core, no scheduler
result. Listed for lineage.

---

## Part V — Atomicity, refinement and compositionality

These are the logics for proving *concurrent objects* correct under interference — the toolbox for
P0, P1 and P8. Most are historical; read them for the technique, not to build on. Where the
mechanization still builds, that is noted.

**39. RGSep.** Vafeiadis & Parkinson, "A marriage of rely/guarantee and separation logic",
CONCUR 2007. Rely/guarantee (interference) fused with separation logic (local resource), with a
**stability** obligation at its centre. Vafeiadis' thesis (*Modular fine-grained concurrency
verification*, Cambridge 2007, TR `UCAM-CL-TR-726`) proves **linearizability of a Treiber stack and a
lock-free queue** and *derives lock-freedom* from the guarantee condition — the earliest demonstration
that progress properties can fall out of an interference discipline. Soundness is mechanized in Coq
(`vafeiadis/cslsound`, Rocq 8.20.1). ⭐ read for P0+P8.

**40. LRG.** Feng, "Local rely-guarantee reasoning", POPL 2009, DOI `10.1145/1480881.1480922`.
⚠️ Attribution note: it is **Feng**, not Hobor & Gotsman, who are usually credited with it in
second-hand lists.

**41. FCSL.** Nanevski, Ley-Wild et al., "Communicating state transition systems for fine-grained
concurrent resources", PLDI 2015; "Concurrent data structures linked in time", ECOOP 2017. The
`fcsl-pcm` library (`imdea-software/fcsl-pcm`) is **maintained in Rocq**, so the underlying PCM
machinery is usable today.

**42. TaDA.** da Rocha Pinto, Dinsdale-Young & Gardner, "TaDA: A Logic for Time and Data Abstraction",
ECOOP 2014, DOI `10.1007/978-3-662-44202-9_9`. Atomicity itself becomes a resource you can reason
about — the cleanest formulation of *atomicity refinement*, which is exactly the shape of argument
that relates a fine-grained deque to a coarse-grained deque spec.

**43. TaDA Live.** D'Osualdo, Sutherland, Farzan & Gardner, POPL 2022 / TOPLAS, DOI `10.1145/3477082`;
arXiv:1901.05750. → **Liveness** for concurrent objects with atomicity. Relevant to P2/P9.

**44. Elmas, Qadeer & Tasiran, "A calculus of atomic actions."** POPL 2009,
DOI `10.1145/1480881.1480885`. Reduction-style reasoning: proving a block atomic by showing its
interleaved execution is equivalent to a serial one.

**45. Liang & Feng, "Modular verification of linearizability with non-fixed linearization points."**
PLDI 2013, DOI `10.1145/2462156.2462189`. ⭐ **Directly relevant to our T3.** This is the most general
existing treatment of *non-fixed* linearization points — precisely the phenomenon that forced Parabs
to invent "wise" and "multiplexed" prophecy variables for the deque's `pop` failure case.

**46. Liang & Feng, "A program logic for concurrent objects under fair scheduling."** POPL 2016.
→ Fairness *as a hypothesis in the logic*, which is the honest way to handle P9.

**47. RGSim / RGSim-T.** Liang, Feng & Fu, POPL 2012 and TOPLAS 36(1), 2014; Liang, Feng & Shao,
"Compositional verification of termination-preserving refinement of concurrent programs", CSL-LICS
2014. → **Refinement between concurrent programs** — the technique behind P8.

**48. Khyzha, Gotsman & Parkinson, "A generic logic for proving linearizability."** FM 2016,
arXiv:1609.01171.

**49. Vale & Shao, "A compositional theory of linearizability."** POPL 2023 / JACM 71(2), 2024,
`flint.cs.yale.edu/flint/publications/ctlinear.pdf`. → The current theory of composing linearizable
objects — the foundation for claiming a *scheduler* is linearizable from its parts.

**50. Herlihy & Wing, "Linearizability: A correctness condition for concurrent objects."** ACM TOPLAS
12(3):463–492, 1990, DOI `10.1145/78969.78972`. → The definition everything above is about.

**51. LHL: a complete program logic for compositional linearizability.** ECOOP 2026,
DOI `10.4230/LIPIcs.ECOOP.2026.11`.

### Transferable techniques

1. **Layered refinement / certified abstraction layers** (CertiKOS, #33). Define a pure scheduler
   abstract spec, then prove each concrete worker/deque operation refines it by forward simulation.
   Verify a worker module *once* against its deep spec, then stop looking at it.
2. **Environment contexts** (#33) — per-worker reasoning under a *rely* describing the other workers,
   never the whole machine. This is what makes a *P*-worker scheduler proof tractable instead of a
   *P*-thread interference argument.
3. **Atomicity as a resource** (TaDA, #42) plus **non-fixed linearization points** (#45) — the
   combination needed to state the deque spec and then relate it to the scheduler loop.
4. **Fairness as an explicit hypothesis** (#46, and the mCertiKOS Lemma 6 caveat) — the honest way to
   state P9, and the way to keep the plan from overclaiming.
5. **A timeline/timing abstraction** (#34) — if we ever state a *bound* about the implementation
   rather than the DAG, this is the design to copy.

---

## Part VI — Memory models

**16. Batty et al., "Mathematical Foundations of C++ Concurrency."** POPL 2011. →
C11 (the model Lean's runtime's atomics rest on).
**17. Lahav, Vafeiadis, Kang, Hur & Dreyer, "Repairing Sequential Consistency in C/C++11."** PLDI
2017. → **RC11**, the repaired model used by essentially every modern proof and verifier.
**18. Sarkar et al., "Understanding POWER Multiprocessors."** PLDI 2011; **Mador-Haim et al.**,
axiomatic POWER/ARM. → The models Lê et al. prove against.
**19. Rust `Waker` contract.** `doc.rust-lang.org/std/task/trait.Wake.html`. → The *executor-side*
obligation in Rust ("to avoid missed wakeups, all executors must adhere…"). This is the prose
specification of a runtime fact we intend to prove (P6) rather than assume. Value: **[the spec we are
trying to beat]**.

Read 16–18 only if we attempt T3. Default plan: **restrict to `seq_cst`** and say so. Lean's runtime
already uses C++11 `seq_cst` atomics for refcounts and task fields, so an SC assumption is not
unreasonable — but it must be *stated*, not implied.

---

## Part VII — Rust-side tools (relevant only if parts stay in Rust)

**20. RustBelt** (POPL 2018) — foundational soundness of Rust's type system incl. `Send`/`Sync` and
data-race freedom. **21. RefinedRust / RefinedRust2** (PLDI 2024; OOPSLA 2026) — Iris type system for
**unsafe** Rust; the best match if `leanin` keeps a Rust core. **22. Verus** + **VerusSync** +
**VerusBelt** (PLDI 2026) — deductive Rust verification with a concurrency story on a foundational
footing. **23. Kani** — bounded model checking; a bug-finder, not a prover; loop/function contracts
give bounded unbounded-ness. **24. Miri** — interpreter that detects UB and **data races**; ships its
own randomised concurrency scheduler. **25. Loom** (Tokio's own) — exhaustive bounded interleaving
testing of atomics. **26. shuttle** (AWS Labs) — randomised concurrency testing with probabilistic
bug-finding guarantees.

Value: **all of these are dynamic or bounded except RustBelt/RefinedRust/VerusBelt**, which verify
Rust *as written* and give no Lean-side theorem. The dynamic ones (Miri, Loom, shuttle) are the honest
answer to "how do you test a scheduler you cannot yet prove" — and note that **Tokio itself relies on
them**, which is worth remembering before claiming a proof advantage.

---

## Part VIII — Adjacent systems worth reading for shape, not content

**27. Xia et al., "Interaction Trees: Representing Recursive and Impure Programs in Coq."**
POPL 2020 (Distinguished Paper). DOI `10.1145/3371119`; `github.com/DeepSpec/InteractionTrees`.
→ The canonical way to *model* a stateful, reactive scheduler's traces and interleave them; the
semantic backbone for verified concurrent Coq systems. The user already has `coq-itree 5.2.1`
installed. Directly relevant to T1 (how to get a semantics for the thing you are proving).
**28. ctrees** (`github.com/vellvm/ctrees`) and **Guarded Interaction Trees** (arXiv:2307.08514) — the
extensions that add concurrency/internal nondeterminism. The user has `vellvm` checked out locally.
**29. coq-lsp** — a concurrent language server whose scheduler/cancellation decisions are documented;
same shape of problem as Lean's `Lean.Language` snapshot engine.
**30. F\* Steel**, and its successor **F\* Pulse** — the canonical "prove the concurrent data
structure, not just the test" body of work, in a dependently typed language with separation logic.
The nearest thing to a *language-native* precedent for what we want.
**31. Vellvm** — Rocq semantics of LLVM IR including atomics; the compiled layer our C++ FFI actually
executes on.
**32. Liquid Haskell** — listed to dismiss: no concurrency model, no scheduler case study.

---

## Part IX — What is *missing* (the honest negative results)

Established by directed search, 2026-10-07. These are as load-bearing as the positives.

- ❌ **No formal semantics of Lean's `IO`/`BaseIO`/`Task`/`Promise`/`ST.Ref` concurrency exists** — at
  any level. The `@[extern]` bodies are **placeholder stubs, not models**: `Task.spawn (fn) := ⟨fn ()⟩`
  evaluates eagerly on the current thread; `Ref.get r := inhabitedFromRef r` returns an arbitrary
  inhabitant. Contrast `Array`/`String`/`ByteArray`, whose externs carry correct pure bodies. `Std.WP`
  soundness covers `Id`/`Option`/`Except`/`EStateM` and transformers, with an `omnisemantics`-style
  deep-embedding recipe in `tests/elab/vcgenImp.lean` — but **no `IO`/`Task`/`ST` instance and no
  concurrency**; `BaseIO`'s `MonadAttach` is trivial. `iris-lean` models HeapLang, not Lean's `IO`;
  `lean4lean` covers only the kernel.
- ❌ **No verified work-stealing *runtime* — only deque/scheduler proofs.** Nothing machine-checks a
  full async executor's user-visible properties (no lost wakeups, completion, cancellation
  correctness, fairness) in any prover.
- ⚠️ **Even the verified kernels assume scheduler fairness.** mCertiKOS proves starvation-freedom of
  ticket and MCS locks *only under an explicit fairness assumption on the hardware/OS scheduler*, and
  seL4's abstract specification contains **no scheduling policy at all**. There is no precedent for a
  machine-checked fairness or optimality result about a scheduler's *own* policy.
- ❌ **No machine-checked work-stealing deque, work-stealing scheduler, or scheduling bound in Lean.**
- ❌ **No formalized work/span scheduling theory in *any* proof assistant** — Graham, Brent, DAG
  makespan, list scheduling. Cited as folklore, never re-proved.
- ❌ **No machine-checked proof of a full async executor's user-visible properties** (no lost wakeups,
  completion, cancellation correctness, fairness). Nearest: Parabs in Rocq.
- ❌ **`TASOR` does not exist.** The framework believed to exist under that name
  (Mével/Jourdan/Pottier, "A Theory of Provably-Correct Work Stealing") is not in GitHub repository
  search, the HAL API, Pottier's own publication list, or Mével's homepage. The real candidates are
  Parabs (#7), Parcas (#13), Cosmo (#12) and BWoS (#8).
- ❌ **Lean has no ThreadSanitizer instrumentation and no deterministic scheduler hook.** No
  `Loom`/`shuttle`/`miri` equivalent exists. A deterministic runtime is a *deliverable*, not a tool we
  can reach for.
- ❌ **No Lean-level work/span credits**; `iris-lean` has time receipts only.
- ❌ **No weak-memory Iris instance in Lean.**
