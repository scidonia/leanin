{
  description = "leanin — Tokio-inspired concurrency library and work-stealing scheduler for Lean 4";

  inputs = {
    # nixpkgs tracks `nixos-unstable`; no revision is written here. flake.lock
    # records the revision actually resolved, and `nix flake update nixpkgs`
    # advances it.
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

    flake-parts.url = "github:hercules-ci/flake-parts";

    treefmt-nix.url = "github:numtide/treefmt-nix";
    treefmt-nix.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs =
    inputs@{ flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [ "x86_64-linux" ];

      imports = [ inputs.treefmt-nix.flakeModule ];

      perSystem =
        { config, pkgs, ... }:
        let
          # Lean `v4.35.0-rc3` is the nixpkgs `lean4` derivation with its source
          # and version moved to the pre-release tag, rather than elan: elan
          # resolves `lean-toolchain` by downloading from the network, which an
          # offline run may not do.
          #
          # The 4.35 line (still pre-release) is deliberate rather than
          # incidental: `Std.WP` — the weakest-precondition framework this
          # project's proof strategy leans on — does not exist in v4.34.1 or
          # earlier. Downgrading the toolchain removes the program logic, not
          # just a version number.
          lean4 = pkgs.lean4.overrideAttrs (prev: {
            version = "4.35.0-rc3";
            src = pkgs.fetchFromGitHub {
              owner = "leanprover";
              repo = "lean4";
              tag = "v4.35.0-rc3";
              hash = "sha256-gVqvQ9fdyCFxMiplNl5fQsw3uc3fPrkO2N3RymVAi7Y=";
            };

            # The tag's own `LEAN_SPECIAL_VERSION_DESC` is empty, so a source build would
            # self-report `4.35.0`; upstream builds the RC tarball with `rc3`. The untyped
            # `-D` is deliberate: the tag's top-level CMakeLists forwards command-line
            # variables to the stage builds only while their cache type is still
            # UNINITIALIZED (its own comment: "does not catch `-DFOO:BAR=` typed uses"),
            # and the installed binaries are stage1's `make install`. The version string is
            # also part of the .olean format, so every stage must agree on it.
            cmakeFlags = prev.cmakeFlags ++ [ "-DLEAN_SPECIAL_VERSION_DESC=rc3" ];

            # 4.35 declares three ExternalProjects that clone over the network
            # (`lean4lean`, `nanoda`, `con-leche`); CMake probes for the download tool
            # during configure, so a source build now needs git present. All three are
            # `EXCLUDE_FROM_ALL`, so the default target never clones them and the
            # sandbox's lack of network is not reached. 4.34.1 declared none of them.
            nativeBuildInputs = prev.nativeBuildInputs ++ [ pkgs.gitMinimal ];
          });

          leaninShell = pkgs.mkShell {
            name = "leanin";

            packages = [
              lean4
              pkgs.git
              pkgs.coreutils
              pkgs.zstd
              config.treefmt.build.wrapper
            ];

            shellHook = ''
              # The host may have an unrelated elan/lean on PATH; the pinned
              # toolchain must win, otherwise `lake` would resolve `lean-toolchain`
              # through elan and try to download a toolchain during an offline run.
              export PATH="${lean4}/bin''${PATH:+:$PATH}"

              # Lean elaborates with every core it can find, which on a working
              # desktop starves interactive audio and editors for minutes at a time.
              # `lake` and `lean` are therefore wrapped to run under `nice -n 19` by
              # default. The wrapper execs the pinned binary by absolute path, so the
              # tool, its version, arguments, output and exit status are the pinned
              # ones and only the scheduling priority differs.
              #
              # Targets are written from `${lean4}/bin`, never from a
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
                    printf '#!/bin/sh\nexec nice -n 19 %s "$@"\n' "${lean4}/bin/$leanin_tool" \
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
                  lake() { command "${pkgs.coreutils}/bin/nice" -n 19 "${lean4}/bin/lake" "$@"; }
                  lean() { command "${pkgs.coreutils}/bin/nice" -n 19 "${lean4}/bin/lean" "$@"; }
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
          treefmt = {
            projectRootFile = "flake.nix";

            programs = {
              deadnix.enable = true;
              mdformat.enable = true;
              nixfmt.enable = true;
              shellcheck.enable = true;
              shfmt.enable = true;
              statix.enable = true;
              taplo.enable = true;
            };
          };

          devShells = {
            default = leaninShell;
            leanin = leaninShell;
          };

          packages = {
            inherit lean4;
            default = leaninShell;
          };
        };
    };
}
