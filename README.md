# `leanin`

A Tokio-inspired concurrency library and work-stealing scheduler for **Lean 4**, with the algorithms
taken from Tokio's Rust source and machine-checked proofs for the properties that matter.

**Status: planning.** The design decisions are settled (D0–D7 in
[`docs/decisions.md`](docs/decisions.md)) and the roadmap in [`PLAN.md`](PLAN.md) follows from them.
Three questions remain open (O1–O3); one of them gates the interface, so no library code has been
written yet beyond the measurement harness.

## Start here

→ **[`docs/decisions.md`](docs/decisions.md)** — what was decided and why.
→ **[`docs/lean-scheduler.md`](docs/lean-scheduler.md)** — what scheduler Lean actually uses today,
read out of the C++ runtime that ships with the toolchain.
→ **[`PLAN.md`](PLAN.md)** — the plan and roadmap.

Supporting documents:

| Document | Contents |
|---|---|
| [`docs/decisions.md`](docs/decisions.md) | D0–D7 settled, O1–O3 open, each with its evidence |
| [`docs/primitive-theory.md`](docs/primitive-theory.md) | What the externs guarantee: axioms, discharge, control tests |
| [`docs/interface.md`](docs/interface.md) | The fixed interface: one spec, two implementations |
| [`docs/lean-scheduler.md`](docs/lean-scheduler.md) | The current scheduler, from runtime source, with measurements |
| [`docs/lean-concurrency-today.md`](docs/lean-concurrency-today.md) | What Lean 4.35 already gives you, and the measured gaps |
| [`docs/tokio-map.md`](docs/tokio-map.md) | What we are stealing from Tokio, component by component |
| [`docs/proof-strategy.md`](docs/proof-strategy.md) | Property ladder, three-layer architecture, TCB, the hard parts |
| [`docs/reading-list.md`](docs/reading-list.md) | Annotated primary sources, with verification status |
| [`docs/evidence.md`](docs/evidence.md) | Every measured and read-first-hand fact, with commands and anchors |

## Build and run

The toolchain is pinned in **two places that must agree**:

| File | For | Pin |
|---|---|---|
| `lean-toolchain` | `elan` users | `leanprover/lean4:v4.35.0-rc3` |
| `flake.nix` | `nix` users | `leanDistribution`, the v4.35.0-rc3 release tarball by SHA-256 |

Both name the same release. The nix path pins the release **tarball** rather than installing through
`elan`, because `elan` resolves `lean-toolchain` by downloading from the network — which an offline
run may not do. This is the same convention `../SpecAMQP` and `../TemperMint` use.

```sh
nix develop -c lake build          # the library, the theory, and every harness below

nix develop -c lake exe spike      # measure Lean's current scheduler
nix develop -c lake exe wakerspike # the Task-as-waker bridge
nix develop -c lake exe controls   # runtime controls for the bridge axioms
```

`lake build` also prints the `#print axioms` audit from `LeanIn/Theory/Bridge.lean`, which reports
what the model's theorems rest on — currently only Lean's built-in `propext` and `Quot.sound`.

The shell runs `lake` and `lean` under `nice -n 19` by default, so elaborating `Std` yields to
anything interactive. `LEANIN_LEAN_NICE=0 nix develop` opts out.

4.35 rather than 4.34 is deliberate: `Std.WP` — the weakest-precondition framework the proof strategy
leans on — does not exist before 4.35, so a downgrade removes the program logic, not just a version
number.

`lake exe spike` is the measurement harness behind the numbers in
[`docs/evidence.md`](docs/evidence.md). It reports the pool size actually used, the cost of blocking
versus non-blocking sleeps under contention, and exercises `IO.asTask`/`IO.wait`, `IO.Promise`,
`Std.Async`, and `Std.Sync.Channel`. It takes about 15 seconds, most of it deliberate sleeps.

## Reference material

`Vendor/tokio/` is a read-only copy of the Tokio source, kept as the algorithm reference so that
"this algorithm came from Tokio" is checkable line by line. It is not part of the build and carries
Tokio's own licence.
