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
