#!/usr/bin/env bash
# A queue's per-operation cost must not rise with its depth. Exit 2 is a setup failure (the build, or the copying
# control not being flagged, which means the detector is blind); exit 1 is a case that rises.
#   nix develop -c bash tests/queue-scaling.sh
set -uo pipefail
cd "$(dirname "$0")/.."
lake build queueScaling >/dev/null || { echo "queue-scaling: setup: build failed"; exit 2; }
out=$(lake exe queueScaling)
status=$?
echo "$out"
case "$status" in
  0) ;;
  1) echo "queue-scaling: a queue's cost rises with depth"; exit 1 ;;
  *) echo "queue-scaling: setup failure (status $status)"; exit 2 ;;
esac
for c in control-array inject timers; do
  grep -q "case=$c|" <<<"$out" || { echo "queue-scaling: setup: no record for $c"; exit 2; }
done
echo "queue-scaling: ok"
