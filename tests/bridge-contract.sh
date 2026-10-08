#!/usr/bin/env bash
# Behaviour checks for the bridge contracts, at the public boundary. See tests/bridge-contract.md.
#
#   nix develop -c bash tests/bridge-contract.sh BT1
#
# This can falsify a contract and cannot establish adequacy. A watchdog bounds a hang; it establishes
# neither timing nor causality.
set -u -o pipefail

readonly WATCHDOG="${LEANIN_WATCHDOG:-300}"
failures=0

setup_error() { printf 'bridge-contract: SETUP ERROR: %s\n' "$1" >&2; printf '  %s\n' "${2:-}" >&2; exit 2; }
note() { printf '%s\n' "$*"; }

bounded() { timeout "$WATCHDOG" "$@"; }

pinned() {
  note "pinned: $(cat lean-toolchain 2>/dev/null || echo '<no lean-toolchain>')"
  note "pinned: $(lean --version 2>&1 | head -1)"
  note "pinned: $(lake --version 2>&1 | tail -1)"
  note "pinned: $(uname -sm)"
}

# --- the record shape ------------------------------------------------------------------------------
# Exactly the five fields, in this order, each nonempty. An extra, missing, transposed, empty or
# duplicated field is rejected, so a near miss that keeps the expected tokens cannot pass.
readonly REC_RE='^bridge\|wait-cycle\|ns=[0-9]+\|actor=(caller|sibling)\|op=(acquired|parking|notified|resumed|released)\|holds=(yes|no)$'

# field_of <records> <actor> <op> <field> — the named field of the single matching record, or nonzero
# when there is not exactly one. Values come from the record, never from the caller.
field_of() {
  local recs="$1" actor="$2" op="$3" key="$4" val
  local -a hits
  mapfile -t hits < <(grep -F "|actor=${actor}|op=${op}|" <<<"$recs" || true)
  [ "${#hits[@]}" -eq 1 ] || return 1
  val="${hits[0]#*|${key}=}"; val="${val%%|*}"
  [ -n "$val" ] || return 1
  printf '%s' "$val"
}

ns_of() {
  local v; v="$(field_of "$1" "$2" "$3" ns)" || return 1
  case "$v" in '' | *[!0-9]*) return 1 ;; esac
  printf '%s' "$v"
}

# check_bt1 — reads records on stdin, prints why on stdout, returns 0 only when every relation holds.
check_bt1() {
  local recs; recs="$(cat)"
  local n; n="$(grep -c . <<<"$recs" || true)"
  [ "$n" -eq 7 ] || { note "    expected 7 records, saw $n"; return 1; }
  local r bad=0
  while IFS= read -r r; do
    [[ "$r" =~ $REC_RE ]] || { note "    record does not match the shape: [$r]"; bad=1; }
  done <<<"$recs"
  [ "$bad" -eq 0 ] || return 1
  # each stage exactly once, with the ownership it claims: a missing or repeated stage is not the cycle
  local s a o h c
  for s in "caller acquired yes" "caller parking yes" "sibling acquired yes" \
           "sibling notified yes" "sibling released no" "caller resumed yes" "caller released no"; do
    read -r a o h <<<"$s"
    c="$(grep -cF "|actor=${a}|op=${o}|holds=${h}" <<<"$recs" || true)"
    if [ "$c" != "1" ]; then note "    expected exactly one '$a $o holds=$h', saw ${c:-0}"; bad=1; fi
  done
  [ "$bad" -eq 0 ] || return 1
  local acq par res not rel sib
  acq="$(ns_of "$recs" caller acquired)"  || { note "    no single caller acquired record"; return 1; }
  par="$(ns_of "$recs" caller parking)"   || { note "    no single caller parking record"; return 1; }
  res="$(ns_of "$recs" caller resumed)"   || { note "    no single caller resumed record"; return 1; }
  rel="$(ns_of "$recs" caller released)"  || { note "    no single caller released record"; return 1; }
  not="$(ns_of "$recs" sibling notified)" || { note "    no single sibling notified record"; return 1; }
  sib="$(ns_of "$recs" sibling acquired)" || { note "    no single sibling acquired record"; return 1; }
  [ "$acq" -lt "$par" ] || { note "    caller acquired ($acq) is not before parking ($par)"; bad=1; }
  [ "$par" -lt "$sib" ] || { note "    the sibling acquired ($sib) before the caller parked ($par): wait did not release the lock"; bad=1; }
  [ "$sib" -lt "$res" ] || { note "    the sibling acquired ($sib) after the caller resumed ($res): the release is not inside the call"; bad=1; }
  [ "$not" -lt "$res" ] || { note "    the caller resumed ($res) before the notification ($not)"; bad=1; }
  [ "$res" -lt "$rel" ] || { note "    the caller released ($rel) before it resumed ($res)"; bad=1; }
  [ "$bad" -eq 0 ]
}

# --- BT1 -------------------------------------------------------------------------------------------
scenario_BT1() {
  note "BT1  the wait cycle, on the narrow path"
  pinned
  local out status
  out="$(bounded lake exe bridgecontrols 2>&1)"; status=$?
  if [ "$status" -eq 0 ]; then note "  ok      BT1  the bridge-controls executable ran"
  else note "  FAIL    BT1  the bridge-controls executable ran (status $status)"; failures=$((failures + 1))
       tail -5 <<<"$out"; return 1; fi
  local recs; recs="$(grep '^bridge|wait-cycle|' <<<"$out" || true)"
  if [ -n "$recs" ]; then note "  ok      BT1  the caller and sibling produced records"
  else note "  FAIL    BT1  the caller and sibling produced records"; failures=$((failures + 1)); return 1; fi

  local why
  if why="$(check_bt1 <<<"$recs")"; then note "  ok      BT1  the recorded trace satisfies every relation"
  else note "  FAIL    BT1  the recorded trace satisfies every relation"; note "$why"; failures=$((failures + 1)); fi

  # The detector's own controls, built from the records this same execution produced.
  local tmp; tmp="$(mktemp -d)"
  printf '%s\n' "$recs" >"$tmp/real"
  accept() {
    if check_bt1 <"$2" >/dev/null 2>&1; then note "  ok      BT1  the detector accepted $1"
    else note "  FAIL    BT1  the detector rejected $1"; failures=$((failures + 1)); fi
  }
  reject() {
    if cmp -s "$tmp/real" "$2"; then
      note "  FAIL    BT1  the mutation for '$1' is identical to the real trace (a silent no-op)"
      failures=$((failures + 1)); return
    fi
    if check_bt1 <"$2" >/dev/null 2>&1; then note "  FAIL    BT1  the detector accepted $1"; failures=$((failures + 1))
    else note "  ok      BT1  the detector rejected $1"; fi
  }
  accept "the real trace" "$tmp/real"
  # The mutations change a *field*, because that is what the checker reads: line order is deliberately
  # not part of the contract, a concurrent trace having none. A swap that moved lines alone would be
  # accepted, and rightly.
  swap_ns() { # swap_ns <out> <patternA> <patternB>
    awk -v OFS='|' -v pa="$2" -v pb="$3" '
      function getns(line,   n,a,i) { n=split(line,a,"|"); for(i=1;i<=n;i++) if (a[i] ~ /^ns=/) return substr(a[i],4); return "" }
      function setns(line,v,  n,a,i,o) { n=split(line,a,"|"); o=""; for(i=1;i<=n;i++){ if (a[i] ~ /^ns=/) a[i]="ns=" v; o=o (i>1?OFS:"") a[i] } return o }
      { n++; rec[n]=$0; if ($0 ~ pa) a=n; if ($0 ~ pb) b=n }
      END{ x=getns(rec[a]); y=getns(rec[b]);
           for(i=1;i<=n;i++){ if(i==a) print setns(rec[i],y); else if(i==b) print setns(rec[i],x); else print rec[i] } }' "$tmp/real" >"$1"
  }
  swap_ns "$tmp/swap" '\|op=parking\|' '\|actor=sibling\|op=acquired\|'
  reject "a trace whose acquisition falls outside the park window" "$tmp/swap"
  swap_ns "$tmp/notify-late" '\|op=notified\|' '\|actor=caller\|op=released\|'
  reject "a trace whose notification follows the resume" "$tmp/notify-late"
  grep -v '|actor=sibling|op=acquired|' "$tmp/real" >"$tmp/missing"
  reject "a trace with a stage missing" "$tmp/missing"
  { head -1 "$tmp/real"; cat "$tmp/real"; } >"$tmp/dup"
  reject "a trace with a stage recorded twice" "$tmp/dup"
  sed 's/|holds=yes$/|holds=yes|extra=1/' "$tmp/real" >"$tmp/extra"
  reject "a trace with a field appended" "$tmp/extra"
  sed 's/|actor=caller|op=parking|/|op=parking|actor=caller|/' "$tmp/real" >"$tmp/transposed"
  reject "a trace with two fields transposed" "$tmp/transposed"
  rm -rf "$tmp"
  return 0
}

case "${1:-BT1}" in
  BT1) scenario_BT1 ;;
  *) setup_error "unknown scenario '${1:-}'" "known: BT1" ;;
esac

note ""
if [ "$failures" -eq 0 ]; then note "bridge-contract: all checks passed"; exit 0; fi
note "bridge-contract: $failures check(s) failed"; exit 1
