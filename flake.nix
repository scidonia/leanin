{
  description = "leanin — Tokio-inspired concurrency library and work-stealing scheduler for Lean 4";

  # The nixpkgs revision is the one `../SpecAMQP` and `../TemperMint` pin, so the
  # Lean environments across these repositories agree. Keep them in step: a
  # repository that pins a different nixpkgs quietly acquires a different
  # clang and libstdc++, and leanin links a native runtime with both.
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/b3d51a0365f6695e7dd5cdf3e180604530ed33b4";

  outputs =
    { self, nixpkgs }:
    let
      system = "x86_64-linux";

      pkgs = import nixpkgs { inherit system; };

      # Lean `v4.35.0-rc3`, pinned by SHA-256 rather than installed through
      # elan: elan resolves `lean-toolchain` by downloading from the network,
      # which an offline run may not do.
      #
      # The 4.35 line (still pre-release; `v4.35.0-rc4` is the newest tag) is
      # deliberate rather than incidental: `Std.WP` — the weakest-precondition
      # framework this project's proof strategy leans on — does not exist in
      # v4.34.1 or earlier. Downgrading the toolchain removes the program logic,
      # not just a version number.
      leanDistribution = pkgs.stdenv.mkDerivation {
        pname = "lean4";
        version = "4.35.0-rc3";

        src = pkgs.fetchurl {
          url = "https://github.com/leanprover/lean4/releases/download/v4.35.0-rc3/lean-4.35.0-rc3-linux.tar.zst";
          hash = "sha256-FSbeFsBJbxa0ahaPJsmQr043llBSc8M0L+wX1y12OZc=";
        };

        nativeBuildInputs = [
          pkgs.autoPatchelfHook
          pkgs.zstd.bin
        ];
        # `gmp`, `uv`, `ssl` and `crypto` are bundled as static archives under
        # `lib/lean` in the release tarball, so the only shared dependency the
        # linked executables need from the host is the C++ standard library.
        buildInputs = [ pkgs.stdenv.cc.cc.lib ];

        sourceRoot = "lean-4.35.0-rc3-linux";
        dontConfigure = true;
        dontBuild = true;

        installPhase = ''
          runHook preInstall
          mkdir -p $out
          cp -r . $out/
          runHook postInstall
        '';
      };

      leaninShell = pkgs.mkShell {
        name = "leanin";

        packages = [
          leanDistribution
          pkgs.git
          pkgs.coreutils
          pkgs.zstd
        ];

        shellHook = ''
          # The host may have an unrelated elan/lean on PATH; the pinned
          # toolchain must win, otherwise `lake` would resolve `lean-toolchain`
          # through elan and try to download a toolchain during an offline run.
          export PATH="${leanDistribution}/bin''${PATH:+:$PATH}"

          # Lean elaborates with every core it can find, which on a working
          # desktop starves interactive audio and editors for minutes at a time.
          # `lake` and `lean` are therefore wrapped to run under `nice -n 19` by
          # default. The wrapper execs the pinned binary by absolute path, so the
          # tool, its version, arguments, output and exit status are the pinned
          # ones and only the scheduling priority differs.
          #
          # Targets are written from `${leanDistribution}/bin`, never from a
          # `command -v` lookup: a lookup can return an exported shell function's
          # name, or some other host tool of the same name, and a wrapper built
          # from that re-enters itself instead of reaching the pinned binary.
          # Installation is all-or-nothing for the same kind of reason: a shell
          # that announces low-priority Lean and then runs it at normal priority
          # is reporting success for something it did not do.
          #
          # LEANIN_LEAN_NICE=0 is the only opt-out: set it before entering the
          # shell for a diagnostic shell that must see an unmodified PATH.
          if [ "''${LEANIN_LEAN_NICE:-1}" != "0" ]; then
            leanin_nice_dir="''${TMPDIR:-/tmp}/leanin-lean-nice"
            leanin_nice_failure=""
            mkdir -p "$leanin_nice_dir" || leanin_nice_failure="mkdir -p $leanin_nice_dir"
            if [ -z "$leanin_nice_failure" ]; then
              for leanin_tool in lake lean; do
                printf '#!/bin/sh\nexec nice -n 19 %s "$@"\n' "${leanDistribution}/bin/$leanin_tool" \
                  >"$leanin_nice_dir/$leanin_tool" &&
                  chmod +x "$leanin_nice_dir/$leanin_tool" ||
                  { leanin_nice_failure="installing the $leanin_tool wrapper in $leanin_nice_dir"; break; }
              done
            fi
            if [ -z "$leanin_nice_failure" ]; then
              export PATH="$leanin_nice_dir:$PATH"
              # The pinned toolchain must win, which the PATH entry above only
              # achieves against executables: in bash a function beats a PATH
              # entry, so an inherited `lake` function would shadow the shim and
              # silently run an unniced, possibly unrelated tool. These
              # definitions close that hole. `export -n` matters: redefining an
              # imported exported function would otherwise inherit its export
              # attribute and hand the function to every child shell, so clearing
              # it is what keeps child processes resolving through the shim.
              lake() { command "${pkgs.coreutils}/bin/nice" -n 19 "${leanDistribution}/bin/lake" "$@"; }
              lean() { command "${pkgs.coreutils}/bin/nice" -n 19 "${leanDistribution}/bin/lean" "$@"; }
              export -nf lake lean
            else
              printf 'leanin: the low-priority Lean shim could not be installed: %s\n' "$leanin_nice_failure" >&2
              printf 'leanin: Lean would run at normal priority, which this shell does not do\n' >&2
              printf 'leanin: set LEANIN_LEAN_NICE=0 if an unshimmed shell is what you want\n' >&2
            fi
          fi

          printf 'leanin: %s\n' "$(lean --version)"
        '';
      };
    in
    {
      devShells.${system} = {
        default = leaninShell;
        leanin = leaninShell;
      };

      packages.${system} = {
        inherit leanDistribution;
        default = leaninShell;
      };
    };
}
