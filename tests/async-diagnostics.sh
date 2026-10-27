#!/usr/bin/env bash
# async-diagnostics.sh — the macro's named diagnostics, and the shapes they reject or accept.
# Run: nix develop -c bash tests/async-diagnostics.sh
set -uo pipefail
cd "$(dirname "$0")/.."
export LEAN_PATH=.lake/build/lib/lean
ok=1

expect_error() { # <file> <phrase>... — each phrase must appear contiguously in the flattened rejection
  # The elaborator wraps diagnostics across lines, so the output is flattened before matching: a phrase that
  # binds an actual type to its expected type must match as one run of text, not as scattered tokens.
  local file="$1"; shift
  local out flat frag
  out="$(lean "tests/async-diagnostics/$file" 2>&1)" && {
    echo "diag: $file elaborated; expected rejection mentioning [$*]" >&2; ok=0; return; }
  flat="$(tr '\n' ' ' <<<"$out" | tr -s ' ')"
  for frag in "$@"; do
    grep -qF "$frag" <<<"$flat" || {
      echo "diag: $file rejected but without [$frag]; got:" >&2; echo "$out" >&2; ok=0; return; }
  done
}

expect_ok() { # <file>
  local out
  out="$(lean "tests/async-diagnostics/$1" 2>&1)" || {
    echo "diag: $1 rejected; expected it to elaborate:" >&2; echo "$out" >&2; ok=0; }
}

expect_error unascribed-field.lean 'cannot determine the type of state field `mystery`'
expect_error destructuring-let.lean 'destructuring `let` is not supported'
expect_ok    unthreaded-param.lean
expect_error sleep-bound-mismatch.lean 'has type Unit but is expected to have type Nat'
expect_error sleep-bound-dead-mismatch.lean 'has type Unit but is expected to have type Nat'
expect_error send-bound-dead-mismatch.lean 'has type Nat → IO Unit but is expected to have type Except IO.Error Unit → IO Unit'
expect_ok    sleep-bound-ok.lean
expect_ok    private-machine.lean
expect_error private-untagged-run.lean 'is not the `run` of a compiled machine'

[ "$ok" = 1 ] && echo "async-diagnostics: all checks passed" || echo "async-diagnostics: FAILED" >&2
[ "$ok" = 1 ]
