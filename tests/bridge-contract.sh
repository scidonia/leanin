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

# --- the record shapes -----------------------------------------------------------------------------
# Exactly the named fields, in this order, each nonempty. An extra, missing, transposed, empty or
# duplicated field is rejected, so a near miss that keeps the expected tokens cannot pass.
readonly BT1_RE='^bridge\|wait-cycle\|ns=[0-9]+\|actor=(caller|sibling)\|op=(acquired|parking|notified|resumed|released)\|holds=(yes|no)$'
readonly BT2_RE='^bridge\|notify-episode\|ns=[0-9]+\|actor=(caller|waker)\|op=(parked|notified|resumed)\|stage=(1|2)$'
readonly BT3_RE='^bridge\|distinct-objects\|ns=[0-9]+\|actor=(claimer|other)\|op=(lock-a|trylock-a|trylock-b|unlock-a)\|out=(acquired|refused|granted|released)$'

# field_of <records> <match> <key> — the named field of the single record containing <match>, or nonzero
# when there is not exactly one. Values come from the record, never from the caller.
field_of() {
  local recs="$1" match="$2" key="$3" val
  local -a hits
  mapfile -t hits < <(grep -F "$match" <<<"$recs" || true)
  [ "${#hits[@]}" -eq 1 ] || return 1
  val="${hits[0]#*|${key}=}"; val="${val%%|*}"
  [ -n "$val" ] || return 1
  printf '%s' "$val"
}

ns_of() {
  local v; v="$(field_of "$1" "$2" ns)" || return 1
  case "$v" in '' | *[!0-9]*) return 1 ;; esac
  printf '%s' "$v"
}

shape_ok() { # shape_ok <records> <regex> <expected count>
  local recs="$1" re="$2" want="$3" n r bad=0
  n="$(grep -c . <<<"$recs" || true)"
  [ "$n" -eq "$want" ] || { note "    expected $want records, saw $n"; return 1; }
  while IFS= read -r r; do
    [[ "$r" =~ $re ]] || { note "    record does not match the shape: [$r]"; bad=1; }
  done <<<"$recs"
  [ "$bad" -eq 0 ]
}

# exactly_one <records> <exact record> — the stage happens once, with the fields it claims
exactly_one() {
  local recs="$1" want="$2" c
  c="$(grep -cxF "$want" <<<"$recs" || true)"
  if [ "$c" != "1" ]; then note "    expected exactly one [$want], saw ${c:-0}"; return 1; fi
}

lt() { # lt <a> <b> <what>
  [ "$1" -lt "$2" ] || { note "    $3: $1 is not before $2"; return 1; }
}

# --- BT1: the wait cycle ---------------------------------------------------------------------------
check_BT1() {
  local recs; recs="$(cat)"
  shape_ok "$recs" "$BT1_RE" 7 || return 1
  local s bad=0
  for s in "caller acquired yes" "caller parking yes" "sibling acquired yes" \
           "sibling notified yes" "sibling released no" "caller resumed yes" "caller released no"; do
    set -- $s
    exactly_one "$recs" "$(grep -F "|actor=$1|op=$2|holds=$3" <<<"$recs" | head -1)" || bad=1
  done
  [ "$bad" -eq 0 ] || return 1
  local acq par res rel not sib
  acq="$(ns_of "$recs" '|actor=caller|op=acquired|')"  || { note "    no single caller acquired record"; return 1; }
  par="$(ns_of "$recs" '|actor=caller|op=parking|')"   || { note "    no single caller parking record"; return 1; }
  res="$(ns_of "$recs" '|actor=caller|op=resumed|')"   || { note "    no single caller resumed record"; return 1; }
  rel="$(ns_of "$recs" '|actor=caller|op=released|')"  || { note "    no single caller released record"; return 1; }
  not="$(ns_of "$recs" '|actor=sibling|op=notified|')" || { note "    no single sibling notified record"; return 1; }
  sib="$(ns_of "$recs" '|actor=sibling|op=acquired|')" || { note "    no single sibling acquired record"; return 1; }
  lt "$acq" "$par" "caller acquired before parking" || bad=1
  lt "$par" "$sib" "sibling acquired after the caller parked (wait released the lock)" || bad=1
  lt "$sib" "$res" "sibling acquired before the caller resumed (release inside the call)" || bad=1
  lt "$not" "$res" "notification before the caller resumed" || bad=1
  lt "$res" "$rel" "caller resumed before releasing" || bad=1
  [ "$bad" -eq 0 ]
}

# --- BT2: two episodes, and no notification survives one -------------------------------------------
check_BT2() {
  local recs; recs="$(cat)"
  shape_ok "$recs" "$BT2_RE" 6 || return 1
  local bad=0 stage s
  for stage in 1 2; do
    for s in "caller parked" "waker notified" "caller resumed"; do
      set -- $s
      exactly_one "$recs" "$(grep -F "|actor=$1|op=$2|stage=$stage" <<<"$recs" | head -1)" || bad=1
    done
  done
  [ "$bad" -eq 0 ] || return 1
  local p1 n1 r1 p2 n2 r2
  p1="$(ns_of "$recs" '|actor=caller|op=parked|stage=1')"   || { note "    no single stage 1 park"; return 1; }
  n1="$(ns_of "$recs" '|actor=waker|op=notified|stage=1')"  || { note "    no single stage 1 notification"; return 1; }
  r1="$(ns_of "$recs" '|actor=caller|op=resumed|stage=1')"  || { note "    no single stage 1 resume"; return 1; }
  p2="$(ns_of "$recs" '|actor=caller|op=parked|stage=2')"   || { note "    no single stage 2 park"; return 1; }
  n2="$(ns_of "$recs" '|actor=waker|op=notified|stage=2')"  || { note "    no single stage 2 notification"; return 1; }
  r2="$(ns_of "$recs" '|actor=caller|op=resumed|stage=2')"  || { note "    no single stage 2 resume"; return 1; }
  lt "$p1" "$n1" "stage 1 park before its notification" || bad=1
  lt "$n1" "$r1" "stage 1 notification before its resume" || bad=1
  lt "$r1" "$p2" "stage 2 parks after stage 1 resumed" || bad=1
  lt "$p2" "$n2" "stage 2 park before its notification" || bad=1
  lt "$n2" "$r2" "stage 2 notification before its resume" || bad=1
  [ "$bad" -eq 0 ]
}

# --- BT3: two live objects are two objects ----------------------------------------------------------
check_BT3() {
  local recs; recs="$(cat)"
  shape_ok "$recs" "$BT3_RE" 4 || return 1
  local bad=0 s
  for s in "claimer lock-a acquired" "other trylock-a refused" "other trylock-b granted" "claimer unlock-a released"; do
    set -- $s
    exactly_one "$recs" "$(grep -F "|actor=$1|op=$2|out=$3" <<<"$recs" | head -1)" || bad=1
  done
  [ "$bad" -eq 0 ] || return 1
  local la ta tb ua
  la="$(ns_of "$recs" '|actor=claimer|op=lock-a|')"    || { note "    no single lock-a record"; return 1; }
  ta="$(ns_of "$recs" '|actor=other|op=trylock-a|')"   || { note "    no single trylock-a record"; return 1; }
  tb="$(ns_of "$recs" '|actor=other|op=trylock-b|')"   || { note "    no single trylock-b record"; return 1; }
  ua="$(ns_of "$recs" '|actor=claimer|op=unlock-a|')"  || { note "    no single unlock-a record"; return 1; }
  lt "$la" "$ta" "trylock-a after a was locked" || bad=1
  lt "$ta" "$ua" "trylock-a before a was released" || bad=1
  lt "$la" "$tb" "trylock-b after a was locked" || bad=1
  lt "$tb" "$ua" "trylock-b before a was released — the refusal and the grant are in one window" || bad=1
  [ "$bad" -eq 0 ]
}

# --- the harness -----------------------------------------------------------------------------------
accept_with() { # accept_with <id> <label> <checkfn> <file>
  if "$3" <"$4" >/dev/null 2>&1; then note "  ok      $1  the detector accepted $2"
  else note "  FAIL    $1  the detector rejected $2"; failures=$((failures + 1)); fi
}

reject_with() { # reject_with <id> <label> <checkfn> <file> <real>
  if cmp -s "$5" "$4"; then
    note "  FAIL    $1  the mutation for '$2' is identical to the real trace (a silent no-op)"
    failures=$((failures + 1)); return
  fi
  if "$3" <"$4" >/dev/null 2>&1; then note "  FAIL    $1  the detector accepted $2"; failures=$((failures + 1))
  else note "  ok      $1  the detector rejected $2"; fi
}

# swap_field <out> <field> <patternA> <patternB> <real> — exchange one field between two records. The
# mutations change a *field*, because that is what the checker reads: line order is deliberately not part
# of the contract, a concurrent trace having none, so a mutation that moved lines alone would be accepted.
swap_field() {
  awk -v OFS='|' -v key="$2" -v pa="$3" -v pb="$4" -v real="$5" '
    function getf(line,   n,a,i) { n=split(line,a,"|"); for(i=1;i<=n;i++) if (a[i] ~ ("^" key "=")) return substr(a[i],length(key)+2); return "" }
    function setf(line,v,  n,a,i,o) { n=split(line,a,"|"); o=""; for(i=1;i<=n;i++){ if (a[i] ~ ("^" key "=")) a[i]=key "=" v; o=o (i>1?OFS:"") a[i] } return o }
    { n++; rec[n]=$0; if ($0 ~ pa) x=n; if ($0 ~ pb) y=n }
    END{ if (!x || !y) { print "SWAP-PATTERN-MISS" > "/dev/stderr"; exit 3 }
         u=getf(rec[x]); v=getf(rec[y]);
         for(i=1;i<=n;i++){ if(i==x) print setf(rec[i],v); else if(i==y) print setf(rec[i],u); else print rec[i] } }' "$5" >"$1"
  local st=$?
  if [ "$st" -ne 0 ]; then
    note "  FAIL    $1  a swap pattern matched no record (awk status $st): the mutation is not what it says"
    failures=$((failures + 1)); : >"$1"
  fi
}

structural_controls() { # structural_controls <id> <checkfn> <real> <tmp> <drop-match>
  local id="$1" fn="$2" real="$3" tmp="$4" drop="$5"
  grep -vF "$drop" "$real" >"$tmp/missing"
  reject_with "$id" "a trace with a stage missing" "$fn" "$tmp/missing" "$real"
  { head -1 "$real"; cat "$real"; } >"$tmp/dup"
  reject_with "$id" "a trace with a stage recorded twice" "$fn" "$tmp/dup" "$real"
  sed 's/$/|extra=1/' "$real" >"$tmp/extra"
  reject_with "$id" "a trace with a field appended" "$fn" "$tmp/extra" "$real"
  awk -F'|' 'BEGIN{OFS="|"} { t=$4; $4=$5; $5=t; print }' "$real" >"$tmp/transposed"
  reject_with "$id" "a trace with two fields transposed" "$fn" "$tmp/transposed" "$real"
}

run_scenario() { # run_scenario <id> <prefix>
  local id="$1" prefix="$2" fn="check_$1" out status recs
  out="$(bounded lake exe bridgecontrols "$3" 2>&1)"; status=$?
  if [ "$status" -eq 0 ]; then note "  ok      $id  the bridge-controls executable ran"
  else note "  FAIL    $id  the bridge-controls executable ran (status $status)"; failures=$((failures + 1)); return 1; fi
  recs="$(grep -F "$prefix" <<<"$out" || true)"
  if [ -n "$recs" ]; then note "  ok      $id  the carriers produced records"
  else note "  FAIL    $id  the carriers produced records"; failures=$((failures + 1)); return 1; fi
  local tmp; tmp="$(mktemp -d)"; printf '%s\n' "$recs" >"$tmp/real"
  local why
  if why="$("$fn" <<<"$recs")"; then note "  ok      $id  the recorded trace satisfies every relation"
  else note "  FAIL    $id  the recorded trace satisfies every relation"; note "$why"; failures=$((failures + 1)); fi
  accept_with "$id" "the real trace" "$fn" "$tmp/real"
  "$id"_mutations "$id" "$fn" "$tmp"
  rm -rf "$tmp"
}

BT1_mutations() {
  local id="$1" fn="$2" tmp="$3"
  swap_field "$tmp/sw" ns '\|op=parking\|' '\|actor=sibling\|op=acquired\|' "$tmp/real"
  reject_with "$id" "a trace whose acquisition falls outside the park window" "$fn" "$tmp/sw" "$tmp/real"
  swap_field "$tmp/nl" ns '\|op=notified\|' '\|actor=caller\|op=released\|' "$tmp/real"
  reject_with "$id" "a trace whose notification follows the resume" "$fn" "$tmp/nl" "$tmp/real"
  structural_controls "$id" "$fn" "$tmp/real" "$tmp" '|actor=sibling|op=acquired|'
}

BT2_mutations() {
  local id="$1" fn="$2" tmp="$3"
  swap_field "$tmp/s1" ns '\|actor=waker\|op=notified\|stage=1' '\|actor=waker\|op=notified\|stage=2' "$tmp/real"
  reject_with "$id" "a trace whose stage 2 notification precedes stage 1" "$fn" "$tmp/s1" "$tmp/real"
  swap_field "$tmp/s2" ns '\|actor=waker\|op=notified\|stage=2' '\|actor=caller\|op=parked\|stage=1' "$tmp/real"
  reject_with "$id" "a trace where the old notification releases the fresh wait" "$fn" "$tmp/s2" "$tmp/real"
  structural_controls "$id" "$fn" "$tmp/real" "$tmp" '|actor=waker|op=notified|stage=2'
}

BT3_mutations() {
  local id="$1" fn="$2" tmp="$3"
  swap_field "$tmp/out" out '\|actor=other\|op=trylock-a' '\|actor=other\|op=trylock-b' "$tmp/real"
  reject_with "$id" "a trace where the held lock was granted and the free one refused" "$fn" "$tmp/out" "$tmp/real"
  swap_field "$tmp/win" ns '\|actor=other\|op=trylock-b' '\|actor=claimer\|op=unlock-a' "$tmp/real"
  reject_with "$id" "a trace whose acquisition falls outside the window" "$fn" "$tmp/win" "$tmp/real"
  structural_controls "$id" "$fn" "$tmp/real" "$tmp" '|actor=other|op=trylock-b|'
}

scenario() {
  note "$1  $2"
  pinned
  run_scenario "$1" "$3" "$4"
  note ""
}

case "${1:-BT1}" in
  BT1) scenario BT1 "the wait cycle, on the narrow path" 'bridge|wait-cycle|' wait-cycle ;;
  BT2) scenario BT2 "two episodes, and no notification outlives its own" 'bridge|notify-episode|' notify-episode ;;
  BT3) scenario BT3 "two live objects are two objects" 'bridge|distinct-objects|' distinct-objects ;;
  *) setup_error "unknown scenario '${1:-}'" "known: BT1 BT2 BT3" ;;
esac

if [ "$failures" -eq 0 ]; then note "bridge-contract: all checks passed"; exit 0; fi
note "bridge-contract: $failures check(s) failed"; exit 1
