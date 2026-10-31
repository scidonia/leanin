import Lake
open System Lake DSL

package leanin where
  version := v!"0.6.0"
  description := "A concurrency runtime and work-stealing scheduler for Lean 4: Tokio's algorithms, an async that compiles to data rather than closures, and machine-checked proofs for the properties that matter."
  keywords := #["concurrency", "scheduler", "async", "runtime", "software-verification", "ffi"]
  license := "Apache-2.0"
  licenseFiles := #["LICENSE", "NOTICE"]
  /- The library needs this toolchain and no other: `Std.WP`, which the proof strategy leans on, does not exist
  before 4.35. Saying so makes `lake update` prefer it for downstream packages rather than resolving them onto a
  toolchain the library cannot build on. -/
  fixedToolchain := true

/-- The **library**: the concurrency toolkit — runtime, scheduler, task/async, data structures, and the model and
theory that verify them. It imports nothing from `LeanIn/Examples/` or `LeanIn/Exe/`. -/
@[default_target] lean_lib LeanIn where
  globs := #[.one `LeanIn,
             .one `LeanIn.Async, .submodules `LeanIn.Async,
             .submodules `LeanIn.Data,
             .submodules `LeanIn.Model,
             .submodules `LeanIn.Runtime,
             .submodules `LeanIn.Http,
             .submodules `LeanIn.Sched,
             .submodules `LeanIn.Task,
             .submodules `LeanIn.Theory]

/-- The socket shim: `c/netuv.c` compiled and archived by Lake rather than by the dev shell, so that a plain
`lake build` produces it and no store path appears in any build flag. Lake traces the source, so editing the C
rebuilds the object and relinks everything that uses it. -/
extern_lib netuv pkg := do
  let srcJob ← inputFile (pkg.dir / "c" / "netuv.c") true
  let oJob ← buildO (pkg.buildDir / "c" / "netuv.o") srcJob
    #["-fPIC", s!"-I{← getLeanIncludeDir}"] #["-O2"]
  buildStaticLib (pkg.buildDir / "lib" / nameToStaticLib "netuv") #[oJob]

/-- Link arguments for the socket layer: the shim Lake builds above (at the package's own build directory), and
the `libuv` it wraps, which stays a system dependency -- `uv.h` and `-luv` are needed to link it at all. -/
def netuvLinkArgs : Array String := #["-L", ".lake/build/lib", "-lnetuv", "-luv"]

/- The library is the only default target, and that is deliberate. Every executable of this package links the
socket shim, so building **any** of them needs `libuv` -- a bare `lake build` is what a registry and a
first-time user run, and it must not need anything outside the Lean toolchain. The executables, and the shim
with them, are built on demand: `lake exe controls`, `lake exe server`, and so on, which is how the fixtures
and `bench/threeway.sh` already reach them. -/

lean_exe controls where
  root := `LeanIn.Exe.Controls
  moreLinkArgs := netuvLinkArgs

lean_exe dynamics where root := `LeanIn.Exe.Dynamics

lean_exe bridgecontrols where root := `LeanIn.Exe.BridgeControls

lean_exe server where
  root := `LeanIn.Exe.Server
  moreLinkArgs := netuvLinkArgs

lean_exe defuncEcho where
  root := `LeanIn.Exe.DefuncEcho
  moreLinkArgs := netuvLinkArgs

lean_exe stdServer where
  root := `LeanIn.Exe.StdServer
  moreLinkArgs := #["-luv"]

lean_exe hello where root := `LeanIn.Exe.Hello

lean_exe asyncRelay where
  root := `LeanIn.Exe.AsyncRelay
  moreLinkArgs := netuvLinkArgs

lean_exe asyncFailure where
  root := `LeanIn.Exe.AsyncFailure
  moreLinkArgs := netuvLinkArgs

lean_exe multiCarrier where
  root := `LeanIn.Exe.MultiCarrier
  moreLinkArgs := netuvLinkArgs

lean_exe queueScaling where
  root := `LeanIn.Exe.QueueScaling
  moreLinkArgs := netuvLinkArgs

lean_exe compatProbe where
  root := `LeanIn.Exe.CompatProbe
  moreLinkArgs := netuvLinkArgs

lean_exe vmScope where
  root := `LeanIn.Exe.VMScope

lean_exe h1Target where
  root := `LeanIn.Exe.H1Target

lean_exe scopeCancel where
  root := `LeanIn.Exe.ScopeCancel
  moreLinkArgs := netuvLinkArgs

lean_exe drainDeadline where
  root := `LeanIn.Exe.DrainDeadline
  moreLinkArgs := netuvLinkArgs

lean_exe stopDeadline where
  root := `LeanIn.Exe.StopDeadline
  moreLinkArgs := netuvLinkArgs

lean_exe asyncResult where
  root := `LeanIn.Exe.AsyncResult
  moreLinkArgs := netuvLinkArgs

lean_exe h1bench where root := `LeanIn.Exe.H1Bench

lean_exe streamEcho where
  root := `LeanIn.Exe.StreamEcho
  moreLinkArgs := netuvLinkArgs

lean_exe stdEcho where
  root := `LeanIn.Exe.StdEcho
  moreLinkArgs := netuvLinkArgs

lean_exe dispatchBench where
  root := `LeanIn.Exe.DispatchBench
  moreLinkArgs := netuvLinkArgs

lean_exe stdBench where
  root := `LeanIn.Exe.StdBench
  moreLinkArgs := netuvLinkArgs
