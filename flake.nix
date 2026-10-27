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
      systems = [
        "x86_64-linux"
        "aarch64-linux"
      ];

      imports = [ inputs.treefmt-nix.flakeModule ];

      perSystem =
        { config, pkgs, ... }:
        let
          # Lean `v4.35.0` is the official binary release, not a source build: the nixpkgs
          # derivation along this line is a release candidate, and overriding it to the final
          # tag would compile Lean from source on first use (an hour or more). This tarball is
          # the exact build `lean-toolchain` names, so an offline run needs no elan download
          # once it is in the store.
          #
          # The 4.35 line is deliberate: `Std.WP` — the weakest-precondition framework this
          # project's proof strategy leans on — does not exist in v4.34.1 or earlier.
          #
          # Each system has its own release tarball, named by the suffix below.
          leanRelease =
            {
              x86_64-linux = {
                suffix = "linux";
                hash = "sha256-colZekRUMkbJInuMrlAXZ+CVzhf21Ei5X8So3Jcmj20=";
              };
              aarch64-linux = {
                suffix = "linux_aarch64";
                hash = "sha256-yPD4o5IOg5cYsTQ+Z4H9gKPpsQJPvNcHjrMPVOgGsCg=";
              };
            }
            .${pkgs.stdenv.hostPlatform.system};
          lean4 = pkgs.stdenv.mkDerivation {
            pname = "lean4";
            version = "4.35.0";
            src = pkgs.fetchurl {
              url = "https://releases.lean-lang.org/lean4/v4.35.0/lean-4.35.0-${leanRelease.suffix}.tar.zst";
              inherit (leanRelease) hash;
            };
            nativeBuildInputs = [ pkgs.autoPatchelfHook pkgs.zstd ];
            buildInputs = [ pkgs.stdenv.cc.cc.lib pkgs.zlib ];
            sourceRoot = "lean-4.35.0-${leanRelease.suffix}";
            unpackPhase = ''
              tar --zstd -xf $src
            '';
            dontStrip = true;
            installPhase = ''
              mkdir -p $out
              cp -a ./. $out/
            '';
          };

          # `nice -n 19` cannot be spelled as a PATH entry, so each pinned tool is
          # wrapped by its own store package. `nix develop` puts the shell's own
          # entries ahead of the caller's PATH, which comes last, so a wrapper listed
          # here wins over both the toolchain's binary and any host `lean`/`lake`.
          niceLean = pkgs.writeShellScriptBin "lean" ''
            if [ "''${LEANIN_LEAN_NICE:-1}" = "0" ]; then exec ${lean4}/bin/lean "$@"; fi
            exec ${pkgs.coreutils}/bin/nice -n 19 ${lean4}/bin/lean "$@"
          '';
          niceLake = pkgs.writeShellScriptBin "lake" ''
            if [ "''${LEANIN_LEAN_NICE:-1}" = "0" ]; then exec ${lean4}/bin/lake "$@"; fi
            exec ${pkgs.coreutils}/bin/nice -n 19 ${lean4}/bin/lake "$@"
          '';

          # The C shim is **not** built here: `lakefile.lean` declares it as an `extern_lib` and compiles it with
          # Lake, so a plain `lake build` produces `libnetuv.a` and links it. Lake traces the source hash, so
          # editing `c/netuv.c` rebuilds the object and relinks the executables that use it.
          leaninShell = pkgs.mkShell {
            name = "leanin";

            packages = [
              # The wrappers must precede `lean4`: the shell's PATH is built in
              # `packages` order, and that ordering is what makes `nice -n 19` win
              # over the toolchain's own binaries.
              niceLean
              niceLake
              lean4
              pkgs.git
              pkgs.coreutils
              pkgs.zstd
              # The event loop for the I/O path: `libuv` is the portable one (epoll on Linux, kqueue on the BSDs
              # and macOS, IOCP on Windows), which a raw `epoll` shim is not. Both outputs are listed so the
              # headers (`dev`) and the shared object (`out`) reach the compiler and the linker.
              pkgs.libuv
              pkgs.libuv.dev
              # The profiler, for the one question it answers: `callgrind` counts instructions, so it says where a
              # request's CPU goes without the I/O waits a wall-clock run is dominated by. In the shell rather than
              # fetched ad hoc, so a profile in `docs/PERFORMANCE.md` is reproducible as printed.
              pkgs.valgrind
              config.treefmt.build.wrapper
            ];

            shellHook = ''
              # A function beats a PATH entry, so an exported `lean`/`lake` function
              # inherited from the caller's environment would shadow the wrappers, in
              # this shell and in every child shell that re-imports it.
              unset -f lake lean

              # Say so if a change to the PATH order ever puts the toolchain's own
              # `lean` first, rather than silently dropping the priority wrapping.
              case "$(command -v lean)" in
                ${niceLean}/bin/lean) ;;
                *) printf 'leanin: lean resolves to %s, not the wrapper %s\n' \
                     "$(command -v lean)" "${niceLean}/bin/lean" >&2 ;;
              esac

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
