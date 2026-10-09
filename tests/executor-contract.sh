#!/usr/bin/env bash
#
# Behaviour checks for the LeanIn single-carrier executor.
#
# Each check drives the public boundary — the `controls` executable and the independent pure-model
# oracle in tests/ModelOracle.lean — and asserts on the records that boundary produced. Nothing here
# calls a private function: the boundary is the executable's stdout and the oracle's records.
#
# A check whose records are absent, repeated, malformed or relational-false exits 1 with the check's
# own assertion text. A failure before the assertion — the executable did not run, the library did
# not build, the oracle produced nothing, an invocation never returned — is a setup error with
# exit 2, so the two are never confused. The watchdog below only bounds an invocation so that a wait
# which never returns cannot hang the command forever; it reads no clock towards any relation and a
# bound expiry is reported as a defect of the invocation, never as an assertion result.
#
# The checks that compare records also exercise the instrument they compare through: a comparator
# asserted to accept a well-formed record pair and to reject plausible near misses cannot quietly
# pass a broken comparison. Such a control that does not hold is a fixture defect and is reported as
# a setup error, separately from the check's assertion.
#
# Usage, from the repository root:
#   nix develop -c bash tests/executor-contract.sh SC1

set -uo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root" || {
  printf 'setup error: cannot enter %s\n' "$repo_root" >&2
  exit 2
}

# Seconds each invocation is allowed before it is bounded. Generous: it bounds a hang, it does not
# budget a run.
watchdog_seconds=300

fail() {
  printf '%s\n' "$1" >&2
  shift
  for detail in "$@"; do printf '  %s\n' "$detail" >&2; done
  exit 1
}

setup_error() {
  printf 'setup error: %s\n' "$1" >&2
  shift
  for detail in "$@"; do printf '  %s\n' "$detail" >&2; done
  exit 2
}

# bounded <command...> — run the invocation under the watchdog.
bounded() {
  timeout "$watchdog_seconds" "$@"
}

# check_status <check> <status> <command...> — a nonzero status is a defect of the invocation, never
# an assertion. 124 is the watchdog bounding it: a wait that never returned produced no record to
# assert on, so it is reported as a defect, naming the check whose invocation was bounded, rather
# than as a pass or a failure of that check.
check_status() {
  local check="$1" status="$2"
  shift 2
  [ "$status" -eq 0 ] && return 0
  if [ "$status" -eq 124 ]; then
    setup_error "$check: the invocation did not finish within ${watchdog_seconds}s — a bounded wait, not a check result" \
      "invocation: $*" \
      "no record was read, so nothing is asserted either way"
  fi
  setup_error "$check: invocation exited $status" "invocation: $*"
}

# tokens <record> — the |-separated fields of a record, one per line, the final line newline
# terminated so a `read` loop delivers the last field instead of stopping at EOF without it.
tokens() {
  printf '%s\n' "$1" | tr '|' '\n'
}

# field <key> <record> — print the value of the record's single `key=` field. Exits nonzero when the
# key is absent, repeated or empty, so a value is never bound from a neighbouring field, from a
# repeat of the key, or from the tail of a longer one.
field() {
  local key="$1" rec="$2" tok n=0 val=""
  while IFS= read -r tok; do
    case "$tok" in
    "$key="*)
      n=$((n + 1))
      val="${tok#"$key="}"
      ;;
    esac
  done < <(tokens "$rec")
  [ "$n" -eq 1 ] && [ -n "$val" ] || return 1
  printf '%s' "$val"
}

# bound_field <variable> <key> <record> <what> — set <variable> to the record's single nonempty `key`
# value, or report a setup error naming <what>. The comparator's controls are built out of the
# oracle's own record through this, so a value the oracle did not produce cannot enter them. It
# writes through `printf -v` rather than stdout so that a setup error here exits this shell instead
# of a command-substitution subshell.
bound_field() {
  local var="$1" key="$2" rec="$3" what="$4" val
  val="$(field "$key" "$rec")" ||
    setup_error "$what has no single nonempty $key field" "record: [$rec]"
  printf -v "$var" '%s' "$val"
}

# record_is <record> <field>... — true when <record> splits into exactly the named `key=value`
# fields, in that order, each nonempty and appearing once. An extra, missing, empty, reordered or
# duplicated field is rejected, so a near miss that keeps the expected tokens cannot pass.
record_is() {
  local rec="$1"
  shift
  local -a want=("$@")
  local tok n=0 k
  while IFS= read -r tok; do
    k="${want[$n]:-}"
    [ -n "$k" ] || return 1
    case "$tok" in
    "$k="?*) : ;;
    *) return 1 ;;
    esac
    n=$((n + 1))
  done < <(tokens "$rec")
  [ "$n" -eq "${#want[@]}" ]
}

# canonical_ok <record> — a canonical operation record is exactly
# `op=<name>|pos=<natural>|task=<identity>|out=<outcome>`: four fields, in that order, each nonempty,
# nothing else.
canonical_ok() {
  local rec="$1" tok n=0
  while IFS= read -r tok; do
    n=$((n + 1))
    case "$n" in
    1) case "$tok" in op=?*) : ;; *) return 1 ;; esac ;;
    2) case "$tok" in
      pos=*) case "${tok#pos=}" in '' | *[!0-9]*) return 1 ;; esac ;;
      *) return 1 ;;
      esac ;;
    3) case "$tok" in task=?*) : ;; *) return 1 ;; esac ;;
    4) case "$tok" in out=?*) : ;; *) return 1 ;; esac ;;
    *) return 1 ;;
    esac
  done < <(tokens "$rec")
  [ "$n" -eq 4 ]
}

# compare_at <index> <left label> <left record> <right label> <right record> — the one parsed-record
# comparator that both the model-versus-implementation comparison and that comparison's own controls
# are built from. It is true when each record is four canonical fields and the `op`, `pos`, `task`
# and `out` values agree pairwise at that input index, every value taken from its own record's named
# field rather than from anywhere the value appears. On a mismatch it names the first disagreeing
# field on stdout and returns nonzero, so a caller reports the mismatch in its own terms — the SC3
# `Then` for the comparison, a fixture defect for a control.
compare_at() {
  local index="$1" llabel="$2" left="$3" rlabel="$4" right="$5" f lv rv
  canonical_ok "$left" ||
    {
      printf 'record %s is not four canonical fields in %s: [%s]' "$index" "$llabel" "$left"
      return 1
    }
  canonical_ok "$right" ||
    {
      printf 'record %s is not four canonical fields in %s: [%s]' "$index" "$rlabel" "$right"
      return 1
    }
  for f in op pos task out; do
    lv="$(field "$f" "$left")" ||
      {
        printf 'record %s has no single nonempty %s field in %s: [%s]' "$index" "$f" "$llabel" "$left"
        return 1
      }
    rv="$(field "$f" "$right")" ||
      {
        printf 'record %s has no single nonempty %s field in %s: [%s]' "$index" "$f" "$rlabel" "$right"
        return 1
      }
    if [ "$lv" != "$rv" ]; then
      printf 'record %s field %s: %s=%s %s=%s' "$index" "$f" "$llabel" "$lv" "$rlabel" "$rv"
      return 1
    fi
  done
  return 0
}

# trace_ok <trace> — true when <trace> is one or more canonical records joined by exactly one `;`
# between neighbours: no leading, trailing or doubled separator. Word splitting on IFS silently
# drops the empty fields those separators leave, so the separator structure is rejected before
# splitting, and every record that remains must still pass canonical_ok.
trace_ok() {
  local trace="$1" rec n=0
  [ -n "$trace" ] || return 1
  case "$trace" in
  ';'* | *';' | *';;'*) return 1 ;;
  esac
  local IFS=';'
  for rec in $trace; do
    canonical_ok "$rec" || return 1
    n=$((n + 1))
  done
  [ "$n" -gt 0 ]
}

# trace_records <trace> — the records of a trace, one per line. The split is exact only once trace_ok
# has rejected empty separators, which is why the detector control checks the shape first.
trace_records() {
  local IFS=';' rec
  for rec in $1; do printf '%s\n' "$rec"; done
}

# record_with <trace> <key> <value> — print the trace's single record whose own `key` field equals
# <value>. Exits nonzero when no record carries it, or when more than one does, so an absent or
# duplicated record fails rather than one of several being silently picked.
record_with() {
  local trace="$1" key="$2" wanted="$3" rec v n=0 found=""
  while IFS= read -r rec; do
    v="$(field "$key" "$rec")" || continue
    if [ "$v" = "$wanted" ]; then
      n=$((n + 1))
      found="$rec"
    fi
  done < <(trace_records "$trace")
  [ "$n" -eq 1 ] || return 1
  printf '%s' "$found"
}

# record_field_count <record> — the number of |-separated fields in a record.
record_field_count() {
  local tok n=0
  while IFS= read -r tok; do n=$((n + 1)); done < <(tokens "$1")
  printf '%s' "$n"
}

# event_index <event> <comma-separated observed events> — the 0-based position of <event>, or
# nonzero when it is absent. The positions of the observed events are the evidence a check reads;
# elapsed time is never consulted.
event_index() {
  local wanted="$1" list="$2" i=0 e
  local IFS=','
  for e in $list; do
    if [ "$e" = "$wanted" ]; then
      printf '%s' "$i"
      return 0
    fi
    i=$((i + 1))
  done
  return 1
}

# require_order <observed events> <event>... — true when every named event is present and the events
# appear in the given order.
require_order() {
  local list="$1"
  shift
  local prev=-1 ev idx
  for ev in "$@"; do
    idx="$(event_index "$ev" "$list")" || return 1
    [ "$idx" -gt "$prev" ] || return 1
    prev="$idx"
  done
  return 0
}

# await_order_ok <order> — true when a check's `order` field is exactly the events one nonblocking
# await recorded, each exactly once, in the order the check names: the continuation registered, the
# sibling's progress on the invoking carrier, the gated completion released, the awaiter resumed.
# The separator shape is rejected before splitting, so a dropped or empty event cannot leave a
# shorter list that still matches; and a value is never matched anywhere but in this named field.
await_order_ok() {
  local order="$1" e n=0
  case "$order" in '' | ','* | *',' | *',,'*) return 1 ;; esac
  local IFS=','
  for e in $order; do
    n=$((n + 1))
    case "$e" in
    await-registered | sibling-done | gate-released | await-completed) : ;;
    *) return 1 ;;
    esac
  done
  [ "$n" -eq 4 ] || return 1
  require_order "$order" await-registered sibling-done gate-released await-completed
}

# id_multiset_is <identity list> <id>... — true when a `queued`/`delivered` field parses to exactly
# the named identities, once each. The field is a bracketed comma-separated list of ids, so a
# dropped, empty, doubled, unknown or extra entry is rejected before any count is compared, and the
# ids are read out of that named field rather than matched anywhere the value appears. Order is not
# significant: the field is a multiset of identities, not a sequence.
id_multiset_is() {
  local list="$1"
  shift
  local -a want=("$@")
  local inner e i n=0 slot
  case "$list" in
  '['*']')
    inner="${list#"["}"
    inner="${inner%"]"}"
    ;;
  *) return 1 ;;
  esac
  case "$inner" in '' | ',' | ','* | *',' | *',,'*) return 1 ;; esac
  local IFS=','
  for e in $inner; do
    n=$((n + 1))
    slot=-1
    for i in "${!want[@]}"; do
      if [ "${want[$i]}" = "$e" ]; then
        slot="$i"
        break
      fi
    done
    [ "$slot" -ge 0 ] || return 1
    want[slot]=""
  done
  [ "$n" -eq "${#want[@]}" ]
}

# id_sequence_is <identity list> <id>... — true when a `fifo`/`lifo`/`flush` field parses to exactly
# the named identities, in exactly the named order, once each. The field is read with the same
# bracketed comma-separated syntax id_multiset_is accepts, so a dropped, empty, doubled, unknown or
# extra entry is rejected; unlike id_multiset_is the order *is* the assertion, because these fields
# are receipt sequences, and a token-preserving reordering is exactly the defect they must catch.
id_sequence_is() {
  local list="$1"
  shift
  local -a want=("$@")
  local inner e i=0
  case "$list" in
  '['*']')
    inner="${list#"["}"
    inner="${inner%"]"}"
    ;;
  *) return 1 ;;
  esac
  case "$inner" in '' | ',' | ','* | *',' | *',,'*) return 1 ;; esac
  local IFS=','
  for e in $inner; do
    [ "$i" -lt "${#want[@]}" ] || return 1
    [ "${want[$i]}" = "$e" ] || return 1
    i=$((i + 1))
  done
  [ "$i" -eq "${#want[@]}" ]
}

# event_stream_is <event list> <event>... — true when a `phase` field parses to exactly the named
# events, once each, in exactly the named order. The field is a bare comma-separated event stream
# like `order` and `observed`, so its separator shape is rejected before splitting and every event is
# read out of this named field; the order *is* the assertion, because a stream that recorded the same
# events in another order is exactly the defect this detector must catch.
event_stream_is() {
  local list="$1"
  shift
  local -a want=("$@")
  local e i=0
  case "$list" in '' | ','* | *',' | *',,'*) return 1 ;; esac
  local IFS=','
  for e in $list; do
    [ "$i" -lt "${#want[@]}" ] || return 1
    [ "${want[$i]}" = "$e" ] || return 1
    i=$((i + 1))
  done
  [ "$i" -eq "${#want[@]}" ]
}

# bracketed <id>... — render identities in the field syntax the checks parse, `[a,b,...]`, so a
# detector's control is fed the expectation it was built from rather than a retyped string.
bracketed() {
  local IFS=','
  printf '[%s]' "$*"
}

# comma_list <event>... — render a bare comma-separated list, the field syntax a `phase`/`order`
# stream uses, so a detector's control is fed the expectation it was built from rather than a retyped
# string.
comma_list() {
  local IFS=','
  printf '%s' "$*"
}

# The trace body of an `exec|replay|seed=<seed>|<trace>` record.
replay_trace() {
  local rec="$1" rest
  case "$rec" in
  exec\|replay\|seed=*\|*) : ;;
  *) return 1 ;;
  esac
  rest="${rec#exec|replay|seed=}"
  printf '%s' "${rest#*|}"
}

# First record where two ;-separated canonical traces differ.
first_differing_record() {
  local IFS=';' a b i
  read -r -a a <<<"$1"
  read -r -a b <<<"$2"
  i=0
  while [ "$i" -lt "${#a[@]}" ] || [ "$i" -lt "${#b[@]}" ]; do
    if [ "${a[$i]:-}" != "${b[$i]:-}" ]; then
      printf 'record %d: [%s] vs [%s]' "$i" "${a[$i]:-}" "${b[$i]:-}"
      return
    fi
    i=$((i + 1))
  done
  printf 'records match record-for-record'
}

# The control executable prints an affirmative baseline header before any observation.
require_header() {
  case "$1" in
  *"controls for the bridge axioms"*) : ;;
  *) setup_error "the control executable did not print its baseline header" \
    "stdout began: $(printf '%s' "$1" | head -c 200)" ;;
  esac
}

# --- the await-order detector's own control, run inside the SC1 invocation ————————————————————————
# The sibling-before-release relation is only as strong as await_order_ok: a detector that accepted
# a reversed or sibling-less stream would let a blocking await pass, and one that rejected the
# genuine stream would fail a correct run. Before the executor's record is read, assert the
# detector's contract on the complete stream this check names and on the two near misses it must
# reject: the same events with the gate released before the sibling progressed, and the stream a
# blocking await would leave, in which the sibling never progresses at all. These are checks on the
# detector, so a control that does not hold is a fixture defect reported as a setup error, never as
# the SC1 Then. The streams are written here rather than taken from an invocation because the
# detector's contract is shaped by the record syntax alone, not by any value the executor produced.
check_await_order_detector() {
  local valid='await-registered,sibling-done,gate-released,await-completed'
  local reversed='await-registered,gate-released,sibling-done,await-completed'
  local no_sibling='await-registered,gate-released,await-completed'
  local -a names=(gate-before-sibling no-sibling-progress)
  local -a streams=("$reversed" "$no_sibling")
  local i

  await_order_ok "$valid" ||
    setup_error "the await-order detector rejects the complete stream it must accept" \
      "order: [$valid]" \
      "the detector's own control, not the SC1 Then"
  printf 'SC1 control: accepted the complete await stream [%s]\n' "$valid"

  for i in "${!streams[@]}"; do
    if await_order_ok "${streams[$i]}"; then
      setup_error "the await-order detector accepted a near miss it must reject: ${names[$i]}" \
        "order: [${streams[$i]}]" \
        "the detector's own control, not the SC1 Then"
    fi
    printf 'SC1 control: rejected %s [%s]\n' "${names[$i]}" "${streams[$i]}"
  done
}

# --- SC1 — the awaiter yields to its sibling on the invoking carrier before the gated wake.
check_sc1() {
  local out status line caller body sibling waker result order
  local -a records=()

  check_await_order_detector

  out="$(bounded lake exe controls --executor-single)"
  status=$?
  check_status SC1 "$status" "lake exe controls --executor-single"
  require_header "$out"

  mapfile -t records < <(grep '^exec|single|' <<<"$out" || true)
  [ "${#records[@]}" -eq 1 ] ||
    fail "SC1 Then: caller task must yield to sibling before external wake" \
      "expected exactly one exec|single| record, saw ${#records[@]}"
  line="${records[0]}"

  record_is "${line#exec|single|}" caller body sibling waker result order ||
    fail "SC1 Then: caller task must yield to sibling before external wake" \
      "the record is not exactly caller/body/sibling/waker/result/order with nonempty values: [$line]"

  caller="$(field caller "$line")" ||
    fail "SC1 Then: caller task must yield to sibling before external wake" \
      "no single nonempty caller field: [$line]"
  body="$(field body "$line")" ||
    fail "SC1 Then: caller task must yield to sibling before external wake" \
      "no single nonempty body field: [$line]"
  sibling="$(field sibling "$line")" ||
    fail "SC1 Then: caller task must yield to sibling before external wake" \
      "no single nonempty sibling field: [$line]"
  waker="$(field waker "$line")" ||
    fail "SC1 Then: caller task must yield to sibling before external wake" \
      "no single nonempty waker field: [$line]"
  result="$(field result "$line")" ||
    fail "SC1 Then: caller task must yield to sibling before external wake" \
      "no single nonempty result field: [$line]"
  order="$(field order "$line")" ||
    fail "SC1 Then: caller task must yield to sibling before external wake" \
      "no single nonempty order field: [$line]"

  [ "$body" = "$caller" ] ||
    fail "SC1 Then: caller task must yield to sibling before external wake" \
      "caller=$caller body=$body: the body did not run on the invoking caller thread"
  [ "$sibling" = "$caller" ] ||
    fail "SC1 Then: caller task must yield to sibling before external wake" \
      "caller=$caller sibling=$sibling: the sibling did not progress on the invoking carrier"
  [ "$waker" != "$caller" ] ||
    fail "SC1 Then: caller task must yield to sibling before external wake" \
      "caller=$caller waker=$waker: the body ran on the waker thread"
  [ "$result" = "7" ] ||
    fail "SC1 Then: caller task must yield to sibling before external wake" \
      "result=$result: the awaited task did not return 7"
  await_order_ok "$order" ||
    fail "SC1 Then: caller task must yield to sibling before external wake" \
      "order=[$order]: the recorded events do not show the sibling's progress before the gate release"

  printf 'SC1 ok: caller=%s body=%s sibling=%s waker=%s result=%s order=%s\n' \
    "$caller" "$body" "$sibling" "$waker" "$result" "$order"
}

# --- the staged-delivery detector's own control, run inside the SC2 invocation ————————————————————
# The shutdown claim is only as strong as id_multiset_is: a detector that accepted an empty or
# duplicated delivery would let a shutdown that completed nothing pass beside a `remaining=0`, and one
# that bound the staging order would fail a correct run whose bodies finished in another order. Before
# the executor's record is read, assert the detector's contract on the staged identities — it accepts
# them in either delivery order — and on the two near misses it must reject: an empty delivery beside
# `remaining=0`, and a duplicated `31` with `32` missing beside `remaining=0`. These are checks on the
# detector, so a control that does not hold is a fixture defect reported as a setup error, never as
# the SC2 Then, and the near misses never stand in for the executor's own receipts.
check_staged_delivery_detector() {
  local -a staged=(31 32)
  local wellformed='[31,32]' reversed='[32,31]' empty='[]' duplicated='[31,31]'

  id_multiset_is "$wellformed" "${staged[@]}" ||
    setup_error "the staged-delivery detector rejects the identities it must accept" \
      "delivered: [$wellformed]" \
      "the detector's own control, not the SC2 Then"
  printf 'SC2 control: accepted the staged deliveries [%s]\n' "$wellformed"

  id_multiset_is "$reversed" "${staged[@]}" ||
    setup_error "the staged-delivery detector treats the staging order as significant" \
      "delivered: [$reversed]" \
      "the detector's own control, not the SC2 Then"
  printf 'SC2 control: accepted the same identities delivered in the other order [%s]\n' "$reversed"

  if id_multiset_is "$empty" "${staged[@]}"; then
    setup_error "the staged-delivery detector accepted an empty delivery beside remaining=0" \
      "delivered: [$empty] remaining=0" \
      "the detector's own control, not the SC2 Then"
  fi
  printf 'SC2 control: rejected an empty delivery beside remaining=0 [%s]\n' "$empty"

  if id_multiset_is "$duplicated" "${staged[@]}"; then
    setup_error "the staged-delivery detector accepted a duplicated 31 with 32 missing beside remaining=0" \
      "delivered: [$duplicated] remaining=0" \
      "the detector's own control, not the SC2 Then"
  fi
  printf 'SC2 control: rejected a duplicated delivery with an identity missing beside remaining=0 [%s]\n' "$duplicated"
}

# --- SC2 — an injected completion wakes a waiting blockOn in both event orders, and shutdown
# delivers the staged ready work exactly once each.
check_sc2() {
  local out status line before after observed queued delivered remaining
  local -a records=()
  local -a staged=(31 32)

  check_staged_delivery_detector

  out="$(bounded lake exe controls --executor-park)"
  status=$?
  check_status SC2 "$status" "lake exe controls --executor-park"
  require_header "$out"

  mapfile -t records < <(grep '^exec|park|' <<<"$out" || true)
  [ "${#records[@]}" -eq 1 ] ||
    fail "SC2 Then: wake and queued shutdown deliveries not observed exactly once" \
      "expected exactly one exec|park| record, saw ${#records[@]}"
  line="${records[0]}"

  record_is "${line#exec|park|}" before after observed queued delivered remaining ||
    fail "SC2 Then: wake and queued shutdown deliveries not observed exactly once" \
      "the record is not exactly before/after/observed/queued/delivered/remaining with nonempty values: [$line]"

  before="$(field before "$line")" ||
    fail "SC2 Then: wake and queued shutdown deliveries not observed exactly once" \
      "no single nonempty before field: [$line]"
  after="$(field after "$line")" ||
    fail "SC2 Then: wake and queued shutdown deliveries not observed exactly once" \
      "no single nonempty after field: [$line]"
  observed="$(field observed "$line")" ||
    fail "SC2 Then: wake and queued shutdown deliveries not observed exactly once" \
      "no single nonempty observed field: [$line]"
  queued="$(field queued "$line")" ||
    fail "SC2 Then: wake and queued shutdown deliveries not observed exactly once" \
      "no single nonempty queued field: [$line]"
  delivered="$(field delivered "$line")" ||
    fail "SC2 Then: wake and queued shutdown deliveries not observed exactly once" \
      "no single nonempty delivered field: [$line]"
  remaining="$(field remaining "$line")" ||
    fail "SC2 Then: wake and queued shutdown deliveries not observed exactly once" \
      "no single nonempty remaining field: [$line]"

  [ "$before" = "1" ] ||
    fail "SC2 Then: both wake results not observed exactly once" \
      "the pre-notification order completed ${before} times, expected exactly once"
  [ "$after" = "1" ] ||
    fail "SC2 Then: both wake results not observed exactly once" \
      "the parked-first order completed ${after} times, expected exactly once"

  require_order "$observed" pre-notify=emitted-before-park pre-notify=completed ||
    fail "SC2 Then: the pre-notification order was not observed to emit before completing" \
      "observed=$observed"
  require_order "$observed" parked-first=parked producer=emitted-after-park parked-first=completed ||
    fail "SC2 Then: the parked-first completion was not observed after the park and the producer's emission" \
      "observed=$observed"
  event_index drain=0 "$observed" >/dev/null ||
    fail "SC2 Then: shutdown did not drain the queued work" \
      "observed=$observed"

  # The staged ready identities, source-bound: the client's pre-shutdown staging receipt and the
  # receipts of the bodies a shutdown actually ran must both be exactly that staged pair, once each.
  id_multiset_is "$queued" "${staged[@]}" ||
    fail "SC2 Then: wake and queued shutdown deliveries not observed exactly once" \
      "queued=$queued: the staged ready identities ${staged[*]} were not the ones the client recorded as staged"
  id_multiset_is "$delivered" "${staged[@]}" ||
    fail "SC2 Then: wake and queued shutdown deliveries not observed exactly once" \
      "delivered=$delivered: the staged ready identities ${staged[*]} were not each completed exactly once"
  [ "$remaining" = "0" ] ||
    fail "SC2 Then: wake and queued shutdown deliveries not observed exactly once" \
      "remaining=$remaining: shutdown left queued work; remaining only corroborates the receipts above"

  printf 'SC2 ok: before=%s after=%s observed=%s queued=%s delivered=%s remaining=%s\n' \
    "$before" "$after" "$observed" "$queued" "$delivered" "$remaining"
}

# --- SC3 — the implementation's operation records match the pure model's records pairwise.
check_sc3() {
  local impl_out model_out status detail i index
  local -a model_records=() impl_records=()

  impl_out="$(bounded lake exe controls --executor-trace)"
  status=$?
  check_status SC3 "$status" "lake exe controls --executor-trace"
  require_header "$impl_out"

  model_out="$(bounded lake env lean --run tests/ModelOracle.lean)"
  status=$?
  check_status SC3 "$status" "lake env lean --run tests/ModelOracle.lean"

  mapfile -t model_records < <(grep '^model|trace|' <<<"$model_out" || true)
  mapfile -t impl_records < <(grep '^exec|trace|' <<<"$impl_out" || true)

  [ "${#model_records[@]}" -gt 0 ] ||
    setup_error "the model oracle produced no records; the comparison control is missing"

  local n="${#model_records[@]}" m="${#impl_records[@]}"

  # The comparator's own controls, in this same invocation and before it is trusted for the
  # comparison. It must accept a genuine oracle record against itself, and reject two near misses
  # built only from the oracle's own values — the first record with its `task` and `out` values
  # exchanged between those named fields, and the same record with its `pos` value replaced by the
  # oracle's next position. Each near miss must itself be a canonical record, so that its rejection
  # is attributable to the field mismatch and not to its shape. These are checks on the instrument;
  # a control that does not hold is a fixture defect, reported as a setup error, never as the SC3
  # Then below, whose own failure is the model-versus-implementation comparison.
  [ "$n" -ge 2 ] ||
    setup_error "the model oracle produced fewer than two records, so the comparator's one-position control cannot be built" \
      "records: $n"

  local mr
  for index in "${!model_records[@]}"; do
    mr="${model_records[$index]#model|trace|}"
    compare_at "$index" model "$mr" model "$mr" >/dev/null ||
      setup_error "the comparator rejects a genuine oracle record compared with itself" \
        "record $index: [$mr]" \
        "the comparator's own control, not the SC3 Then"
  done

  local m0="${model_records[0]#model|trace|}"
  local m1="${model_records[1]#model|trace|}"
  local op0 pos0 task0 out0 pos1
  op0="$(field op "$m0")" ||
    setup_error "the oracle's first record has no single nonempty op field" "record: [$m0]"
  pos0="$(field pos "$m0")" ||
    setup_error "the oracle's first record has no single nonempty pos field" "record: [$m0]"
  task0="$(field task "$m0")" ||
    setup_error "the oracle's first record has no single nonempty task field" "record: [$m0]"
  out0="$(field out "$m0")" ||
    setup_error "the oracle's first record has no single nonempty out field" "record: [$m0]"
  pos1="$(field pos "$m1")" ||
    setup_error "the oracle's second record has no single nonempty pos field" "record: [$m1]"

  [ "$task0" != "$out0" ] ||
    setup_error "the oracle's first record holds the same value in task and out, so the field-swap control would be vacuous" \
      "record 0: [$m0]"
  [ "$pos1" != "$pos0" ] ||
    setup_error "the oracle's first two records share a position, so the one-position control would be vacuous" \
      "record 0: [$m0]" "record 1: [$m1]"

  local swapped="op=$op0|pos=$pos0|task=$out0|out=$task0"
  local shifted="op=$op0|pos=$pos1|task=$task0|out=$out0"
  canonical_ok "$swapped" ||
    setup_error "the field-swap control is not itself a canonical record" "record: [$swapped]"
  canonical_ok "$shifted" ||
    setup_error "the one-position control is not itself a canonical record" "record: [$shifted]"

  if compare_at 0 model "$m0" control "$swapped" >/dev/null; then
    setup_error "the comparator accepted a record with its task and out values exchanged" \
      "swapped record: [$swapped]" \
      "the comparator's own control, not the SC3 Then"
  fi
  if compare_at 0 model "$m0" control "$shifted" >/dev/null; then
    setup_error "the comparator accepted a record shifted by one input position" \
      "shifted record: [$shifted]" \
      "the comparator's own control, not the SC3 Then"
  fi

  printf 'SC3 control: accepted all %d oracle records against themselves; rejected the task/out swap [%s] and the one-position shift [%s]\n' \
    "$n" "$swapped" "$shifted"

  i=0
  while [ "$i" -lt "$n" ] && [ "$i" -lt "$m" ]; do
    local mv="${model_records[$i]#model|trace|}"
    local ev="${impl_records[$i]#exec|trace|}"
    if ! detail="$(compare_at "$i" model "$mv" implementation "$ev")"; then
      fail "SC3 Then: model trace != implementation trace" \
        "$detail" \
        "model[$i]=[$mv] implementation[$i]=[$ev]"
    fi
    i=$((i + 1))
  done

  if [ "$m" -ne "$n" ]; then
    local -a model_join=() impl_join=()
    local r mj ij
    for r in "${model_records[@]}"; do model_join+=("${r#model|trace|}"); done
    for r in "${impl_records[@]}"; do impl_join+=("${r#exec|trace|}"); done
    mj="$(
      IFS=';'
      printf '%s' "${model_join[*]}"
    )"
    ij="$(
      IFS=';'
      printf '%s' "${impl_join[*]}"
    )"
    fail "SC3 Then: model trace != implementation trace" \
      "model records: $n, implementation records: $m" \
      "model trace: [$mj]" \
      "implementation trace: [$ij]"
  fi

  printf 'SC3 ok: %d records match pairwise\n' "$n"
}

# --- the trace detector's own control, run inside the SC4 invocation ————————————————
# The replay comparison is only as strong as trace_ok: a detector that accepted a malformed trace
# would let a broken comparison pass, and one that rejected a well-formed trace would fail a correct
# replay. Before the replay runs, assert the detector's contract on a well-formed two-record trace —
# it accepts it and parses it as exactly two records of four fields each — and on the five near
# misses the separator rule must reject: an empty trace, one with a leading `;`, one with a trailing
# `;`, one with a doubled `;;`, and one that is a lone `;`. The per-record lookup the failure binding
# reads through is exercised here too: it finds the single record carrying a named field value, and
# rejects a value that no record carries or that two records carry. These are checks on the
# instruments, so a control that does not hold is a fixture defect reported as a setup error, never
# as the SC4 Then. The traces are written here rather than taken from an invocation because these
# contracts are shaped by the record syntax alone, not by any value the executor produced.
check_trace_detector() {
  local valid='op=submit|pos=0|task=0|out=inflight1;op=take|pos=1|task=0|out=taken1'
  local empty='' leading=';op=submit|pos=0|task=0|out=inflight1'
  local trailing='op=submit|pos=0|task=0|out=inflight1;'
  local doubled='op=submit|pos=0|task=0|out=inflight1;;op=take|pos=1|task=0|out=taken1'
  local lone=';'
  local rec nfields nrecords=0
  local -a names=(empty leading-semicolon trailing-semicolon doubled-semicolon lone-semicolon)
  local -a traces=("$empty" "$leading" "$trailing" "$doubled" "$lone")
  local i

  trace_ok "$valid" ||
    setup_error "the canonical-trace detector rejects a well-formed two-record trace" \
      "trace: [$valid]" \
      "the detector's own control, not the SC4 Then"

  while IFS= read -r rec; do
    nfields="$(record_field_count "$rec")"
    [ "$nfields" -eq 4 ] ||
      setup_error "the canonical-trace detector parsed a record of the well-formed trace as $nfields fields, not four" \
        "record: [$rec]" \
        "the detector's own control, not the SC4 Then"
    nrecords=$((nrecords + 1))
  done < <(trace_records "$valid")
  [ "$nrecords" -eq 2 ] ||
    setup_error "the canonical-trace detector parsed the well-formed trace as $nrecords records, not two" \
      "trace: [$valid]" \
      "the detector's own control, not the SC4 Then"

  printf 'SC4 control: accepted the well-formed two-record trace as %d records of four fields each\n' "$nrecords"
  for i in "${!traces[@]}"; do
    if trace_ok "${traces[$i]}"; then
      setup_error "the canonical-trace detector accepted a near miss it must reject: ${names[$i]}" \
        "trace: [${traces[$i]}]" \
        "the detector's own control, not the SC4 Then"
    fi
    printf 'SC4 control: rejected %s [%s]\n' "${names[$i]}" "${traces[$i]}"
  done

  # The per-record lookup the failure binding reads through: it must find the one record carrying a
  # named field value, and reject both a value no record carries and a value two records carry.
  local hit
  hit="$(record_with "$valid" pos 1)" ||
    setup_error "the record lookup found no single record carrying a position that is present" \
      "trace: [$valid]" \
      "the detector's own control, not the SC4 Then"
  [ "$(field task "$hit")" = "0" ] ||
    setup_error "the record lookup returned a record whose task field is not the one at that position" \
      "record: [$hit]" \
      "the detector's own control, not the SC4 Then"
  if record_with "$valid" pos 9 >/dev/null; then
    setup_error "the record lookup accepted a position no record carries" \
      "trace: [$valid]" \
      "the detector's own control, not the SC4 Then"
  fi
  local shared='op=submit|pos=0|task=0|out=inflight1;op=take|pos=0|task=0|out=taken1'
  if record_with "$shared" pos 0 >/dev/null; then
    setup_error "the record lookup picked one of two records carrying the same position" \
      "trace: [$shared]" \
      "the detector's own control, not the SC4 Then"
  fi
  printf 'SC4 control: the record lookup bound pos=1 to task=0 and rejected an absent and a shared position\n'
}

# --- SC4 — a staged scripted failure replays to byte-identical traces; an alternate script differs.
check_sc4() {
  local seed="7" status l1 l2 l3 t1 t2 t3 s1 s2 s3
  local out1 out2 out3
  local -a r1=() r2=() r3=()
  # The staged failing script: the main script fails task identity 1 at input position 3 with the
  # outcome `error:seeded-failure`, and the alternate script delivers identity 2 at that position
  # instead, so the two traces differ by construction rather than by chance.
  local fail_pos="3" fail_task="1" fail_out="error:seeded-failure" alternate_task="2"
  local main_trace fr pos_v task_v out_v alt_at alt_slot

  check_trace_detector

  out1="$(bounded lake exe controls --executor-replay --seed="$seed" --script=main)"
  status=$?
  check_status SC4 "$status" "lake exe controls --executor-replay --seed=$seed --script=main (run 1)"
  require_header "$out1"
  mapfile -t r1 < <(grep '^exec|replay|' <<<"$out1" || true)

  out2="$(bounded lake exe controls --executor-replay --seed="$seed" --script=main)"
  status=$?
  check_status SC4 "$status" "lake exe controls --executor-replay --seed=$seed --script=main (run 2)"
  require_header "$out2"
  mapfile -t r2 < <(grep '^exec|replay|' <<<"$out2" || true)

  out3="$(bounded lake exe controls --executor-replay --seed="$seed" --script=alternate)"
  status=$?
  check_status SC4 "$status" "lake exe controls --executor-replay --seed=$seed --script=alternate"
  require_header "$out3"
  mapfile -t r3 < <(grep '^exec|replay|' <<<"$out3" || true)

  [ "${#r1[@]}" -eq 1 ] && [ "${#r2[@]}" -eq 1 ] && [ "${#r3[@]}" -eq 1 ] ||
    fail "SC4 Then: canonical failure trace absent, cannot replay" \
      "expected exactly one exec|replay| record per invocation, saw $((${#r1[@]} + ${#r2[@]} + ${#r3[@]})) over three"

  l1="${r1[0]}"
  l2="${r2[0]}"
  l3="${r3[0]}"

  t1="$(replay_trace "$l1")" ||
    fail "SC4 Then: canonical failure trace absent, cannot replay" "main run 1: malformed record [$l1]"
  t2="$(replay_trace "$l2")" ||
    fail "SC4 Then: canonical failure trace absent, cannot replay" "main run 2: malformed record [$l2]"
  t3="$(replay_trace "$l3")" ||
    fail "SC4 Then: canonical failure trace absent, cannot replay" "alternate: malformed record [$l3]"

  s1="$(field seed "$l1")" ||
    fail "SC4 Then: canonical failure trace absent, cannot replay" \
      "main run 1: no single nonempty seed field: [$l1]"
  s2="$(field seed "$l2")" ||
    fail "SC4 Then: canonical failure trace absent, cannot replay" \
      "main run 2: no single nonempty seed field: [$l2]"
  s3="$(field seed "$l3")" ||
    fail "SC4 Then: canonical failure trace absent, cannot replay" \
      "alternate: no single nonempty seed field: [$l3]"

  [ "$s1" = "$seed" ] && [ "$s2" = "$seed" ] && [ "$s3" = "$seed" ] ||
    fail "SC4 Then: a replay record's seed does not match the seed given on the command line" \
      "command seed=$seed, parsed seeds: run1=$s1 run2=$s2 alternate=$s3"

  trace_ok "$t1" ||
    fail "SC4 Then: canonical failure trace absent, cannot replay" \
      "main run 1: not a nonempty run of canonical records [$t1]"
  trace_ok "$t2" ||
    fail "SC4 Then: canonical failure trace absent, cannot replay" \
      "main run 2: not a nonempty run of canonical records [$t2]"
  trace_ok "$t3" ||
    fail "SC4 Then: canonical failure trace absent, cannot replay" \
      "alternate: not a nonempty run of canonical records [$t3]"

  [ "$t1" = "$t2" ] ||
    fail "SC4 Then: replay trace differs for the same seed and script" \
      "seed=$seed script=main" \
      "first differing $(first_differing_record "$t1" "$t2")"

  # The staged failure, bound per trace: each same-seed trace of the main script carries exactly one
  # record with `op=fail`, and that record's own `pos`, `task` and `out` fields are the staged
  # position, identity and outcome — not those tokens appearing somewhere in the trace.
  for main_trace in "$t1" "$t2"; do
    fr="$(record_with "$main_trace" op fail)" ||
      fail "SC4 Then: the staged scripted failure is not reproduced at its position, identity and outcome" \
        "trace: [$main_trace]" \
        "expected exactly one record with op=fail"
    pos_v="$(field pos "$fr")" ||
      fail "SC4 Then: the staged scripted failure is not reproduced at its position, identity and outcome" \
        "failure record: [$fr]" "no single nonempty pos field"
    task_v="$(field task "$fr")" ||
      fail "SC4 Then: the staged scripted failure is not reproduced at its position, identity and outcome" \
        "failure record: [$fr]" "no single nonempty task field"
    out_v="$(field out "$fr")" ||
      fail "SC4 Then: the staged scripted failure is not reproduced at its position, identity and outcome" \
        "failure record: [$fr]" "no single nonempty out field"
    [ "$pos_v" = "$fail_pos" ] && [ "$task_v" = "$fail_task" ] && [ "$out_v" = "$fail_out" ] ||
      fail "SC4 Then: the staged scripted failure is not reproduced at its position, identity and outcome" \
        "failure record: [$fr]" \
        "staged: pos=$fail_pos task=$fail_task out=$fail_out"
    printf 'SC4: a main trace carries one failure record at pos=%s task=%s out=%s\n' "$pos_v" "$task_v" "$out_v"
  done

  [ "$t3" != "$t1" ] ||
    fail "SC4 Then: the alternate script produced the same canonical trace" \
      "seed=$seed: the trace comparison cannot distinguish the two scripts"

  # The alternate script's difference is positional and identities, not chance: at the staged position
  # it carries the alternate identity.
  alt_at="$(record_with "$t3" pos "$fail_pos")" ||
    fail "SC4 Then: the alternate script did not change the staged task identity" \
      "alternate trace: [$t3]" \
      "no single record at the staged position pos=$fail_pos"
  alt_slot="$(field task "$alt_at")" ||
    fail "SC4 Then: the alternate script did not change the staged task identity" \
      "alternate record: [$alt_at]" "no single nonempty task field"
  [ "$alt_slot" = "$alternate_task" ] ||
    fail "SC4 Then: the alternate script did not change the staged task identity" \
      "alternate record at pos=$fail_pos: [$alt_at]" \
      "staged alternate identity $alternate_task, main identity $fail_task"
  printf 'SC4: the alternate trace carries task=%s at pos=%s where the main trace carries task=%s\n' \
    "$alt_slot" "$fail_pos" "$fail_task"

  printf 'SC4 ok: seed=%s main trace identical across two fresh invocations, each with one op=fail at pos=%s task=%s out=%s; alternate trace differs\n' \
    "$seed" "$fail_pos" "$fail_task" "$fail_out"
}

# steps_on <bracketed identity list> <carrier> — true when the list is nonempty and every entry is the
# carrier. The syntax is the one id_sequence_is accepts, checked here for the same reasons: a dropped,
# empty, doubled or extra entry is rejected before any entry is compared.
steps_on() {
  local list="$1" carrier="$2" inner e
  case "$list" in
  '['*']')
    inner="${list#"["}"
    inner="${inner%"]"}"
    ;;
  *) return 1 ;;
  esac
  case "$inner" in '' | ',' | ','* | *',' | *',,'*) return 1 ;; esac
  local IFS=','
  for e in $inner; do
    [ "$e" = "$carrier" ] || return 1
  done
  return 0
}

# --- SC6 — real work runs on one carrier, and a pool worker only ever enqueues ————————————————————————
check_sc6() {
  local out status line caller steps external value remaining
  local -a records=()
  # The two numbers the program's own value is the sum of, named here because the contract names them.
  local child_value=11 external_value=5
  local expect_value=$((child_value + external_value))

  # The measurement's own control, before the invocation is read: the detector must accept a list of one
  # thread and reject a list carrying another, or a runtime that quietly handed a body to the pool would pass.
  steps_on '[9,9]' '9' ||
    setup_error "the carrier-only step detector rejects a list of one thread" \
      "steps: [[9,9]]" \
      "the detector's own control, not the SC6 Then"
  if steps_on '[9,8]' '9'; then
    setup_error "the carrier-only step detector accepted a step that ran on another thread" \
      "steps: [[9,8]]" \
      "the detector's own control, not the SC6 Then"
  fi
  printf 'SC6 control: the carrier-only detector accepted two steps on one thread and rejected a foreign one\n'

  out="$(bounded lake exe controls --runtime-threads)"
  status=$?
  check_status SC6 "$status" "lake exe controls --runtime-threads"
  require_header "$out"

  mapfile -t records < <(grep '^exec|runtime|' <<<"$out" || true)
  [ "${#records[@]}" -eq 1 ] ||
    fail "SC6 Then: the runtime did not report where its steps ran" \
      "expected exactly one exec|runtime| record, saw ${#records[@]}"
  line="${records[0]}"

  record_is "${line#exec|runtime|}" caller steps external value remaining ||
    fail "SC6 Then: the runtime did not report where its steps ran" \
      "the record is not exactly caller/steps/external/value/remaining with nonempty values: [$line]"

  caller="$(field caller "$line")" ||
    fail "SC6 Then: the runtime did not report where its steps ran" "no single nonempty caller field: [$line]"
  steps="$(field steps "$line")" ||
    fail "SC6 Then: the runtime did not report where its steps ran" "no single nonempty steps field: [$line]"
  external="$(field external "$line")" ||
    fail "SC6 Then: the runtime did not report where its steps ran" "no single nonempty external field: [$line]"
  value="$(field value "$line")" ||
    fail "SC6 Then: the runtime did not report where its steps ran" "no single nonempty value field: [$line]"
  remaining="$(field remaining "$line")" ||
    fail "SC6 Then: the runtime did not report where its steps ran" "no single nonempty remaining field: [$line]"

  # Every step the runtime ran, on the thread the caller started it on.
  steps_on "$steps" "$caller" ||
    fail "SC6 Then: a task step ran off the caller's thread" \
      "steps=$steps caller=$caller" \
      "the single-carrier claim is that the driver, every body and every resumption are one thread"

  # …and the measurement is not vacuous: another thread was in the picture and was observed.
  [ "$external" != "$caller" ] ||
    fail "SC6 Then: no other thread was observable, so the thread identities establish nothing" \
      "external=$external caller=$caller" \
      "the external completion must have run on a pool worker"

  [ "$value" = "$expect_value" ] ||
    fail "SC6 Then: the awaited values did not both arrive" \
      "value=$value" \
      "expected the child's $child_value plus the external completion's $external_value"

  [ "$remaining" = "0" ] ||
    fail "SC6 Then: the runtime held work when the program finished" "remaining=$remaining"

  printf 'SC6 ok: steps=%s all on caller=%s; external=%s is another thread; value=%s; remaining=%s\n' \
    "$steps" "$caller" "$external" "$value" "$remaining"
}

# --- the queue expectation the SC5 checks read, derived from the pool model ————————————————————————
# Every number here is the model's, not an invocation's. The script has two phases. Phase one submits
# 0..256 before taking any, then drains that whole batch. `cap` is 256 (`LeanIn/Model/Pool.lean:52`)
# and the placement rule `Pool.submit` uses keeps the older half of a full ring while moving the
# *newer* half to `inject` (`:119-125`). That direction is Tokio's, and `queue.rs:295` gives the
# reason: intake places work in the first half, so a task found in the second half is provably not one
# just intaken from `inject`. So 257 submissions of 0..256 — split `take (256 / 2)` from
# `drop (256 / 2)` — leave the ring holding 0..127 and the 257th identity 256, and `inject` holding
# 128..255. `Pool.take`'s `takeFromRing` serves the ring before `inject` (`:81-86`), so the batch's
# take receipts are 0..127 and then 256, followed by the spilled 128..255: that is `fifo`. 300 and 301
# are staged only in phase two, after that drain, so neither appears in it.
# Phase two is a fresh tick: the client stages 300,301 as FIFO queue work and local `spawn`s 400
# through the public operation, whose body locally `spawn`s 401, and so on to 403. `lifoCap` is 3
# (`:49`) and `Pool.take` polls the LIFO slot while the tick's allowance lasts and flushes a slot that
# is still occupied once the allowance is spent (`:89-101`), so the slot holds 400, 401, 402 and then
# the still occupied 403 at the fourth decision: the slot receipts are 400,401,402, the pending 403 is
# flushed to `inject`, and the receipts after the flush are the ring's 300,301 followed by that
# flushed 403 — `flush`, a second-phase boundary separate from phase one's `fifo`. The slot
# observations the scheduler records at each decision are therefore 0:400, 1:401, 2:402 and 3:403 —
# the poll count and the identity the slot held before the take or flush.
#
# `fifo`, `lifo`, `flush` and `slotBefore` are receipt *sequences* and are read with id_sequence_is;
# `staged` and `delivered` are identity *multisets* and are read with id_multiset_is, because the
# order the bodies happen to finish in belongs to the client rather than to the claim. `phase` is the
# client's own ordered event stream — the drained first batch, the fresh tick, the two FIFO stagings
# and the root local spawn — and is read with event_stream_is.
queue_expectation() {
  local i
  # The ring's own receipts first — the older half it kept, and the identity that crossed its capacity
  # — then the newer half the placement rule spilled to `inject`.
  expected_fifo=()
  for ((i = 0; i <= 127; i++)); do expected_fifo+=("$i"); done
  expected_fifo+=(256)
  for ((i = 128; i <= 255; i++)); do expected_fifo+=("$i"); done
  expected_lifo=(400 401 402)
  expected_flush=(300 301 403)
  expected_slot=(0:400 1:401 2:402 3:403)
  # The client's own phase events, in the order the decision fixes them: `batch-drained` only once
  # all 257 first-batch takes have returned their receipts, `tick-start` for the fresh tick, then the
  # two FIFO stagings and the root local spawn.
  expected_phase=(batch-drained tick-start stage:300 stage:301 spawn:400)
  expected_staged=()
  for ((i = 0; i <= 256; i++)); do expected_staged+=("$i"); done
  expected_staged+=(300 301)
  for ((i = 400; i <= 403; i++)); do expected_staged+=("$i"); done
}

# --- the queue-receipt detectors' own control, run inside the SC5 invocation ————————————————————————
# The queue claim is only as strong as the three detectors it is read through: id_sequence_is for the
# `fifo`, `lifo`, `flush` and `slotBefore` receipt sequences, id_multiset_is for the `staged` and
# `delivered` identity sets, and event_stream_is for the client's ordered `phase` events. Before the
# executable's record is read, assert their contract on the expectation this check names — the full
# 263-identity receipt set, the modelled receipt order, the modelled slot occupancy
# 0:400,1:401,2:402,3:403, and the ordered phase stream — and on the six near misses they must
# reject: a staged/completed set with one identity duplicated and another missing, a token-preserving
# swap across the capacity crossing that the FIFO order is read through, a LIFO sequence that took a
# fourth poll instead of flushing the pending continuation, an always-empty slot, a phase-one `fifo`
# that carries 300/301 because they were staged before the first batch was drained, and a
# token-preserving `phase` stream that recorded those two stagings before `batch-drained`. These are
# checks on the detectors, so a control that does not hold is a fixture defect reported as a setup
# error, never as the SC5 Then, and every near miss is built from the expectation or the record
# syntax alone, never from the executable's receipts.
check_queue_receipt_detector() {
  local fifo_full lifo_full flush_full slot_full staged_full phase_full duplicated_missing swapped early_staged early_phase fourth_poll empty_slot tmp
  local i e

  queue_expectation

  fifo_full="$(bracketed "${expected_fifo[@]}")"
  lifo_full="$(bracketed "${expected_lifo[@]}")"
  flush_full="$(bracketed "${expected_flush[@]}")"
  slot_full="$(bracketed "${expected_slot[@]}")"
  staged_full="$(bracketed "${expected_staged[@]}")"
  phase_full="$(comma_list "${expected_phase[@]}")"

  id_multiset_is "$staged_full" "${expected_staged[@]}" ||
    setup_error "the staged/completed identity detector rejects the ${#expected_staged[@]}-identity receipt set it must accept" \
      "staged/delivered: [$staged_full]" \
      "the detectors' own control, not the SC5 Then"
  printf 'SC5 control: accepted the %d-identity staged and completed set\n' "${#expected_staged[@]}"

  id_sequence_is "$fifo_full" "${expected_fifo[@]}" ||
    setup_error "the FIFO receipt detector rejects the modelled ring take order it must accept" \
      "fifo: [$fifo_full]" \
      "the detectors' own control, not the SC5 Then"
  id_sequence_is "$lifo_full" "${expected_lifo[@]}" ||
    setup_error "the LIFO receipt detector rejects the modelled slot take order it must accept" \
      "lifo: [$lifo_full]" \
      "the detectors' own control, not the SC5 Then"
  id_sequence_is "$flush_full" "${expected_flush[@]}" ||
    setup_error "the post-flush receipt detector rejects the modelled order it must accept" \
      "flush: [$flush_full]" \
      "the detectors' own control, not the SC5 Then"
  id_sequence_is "$slot_full" "${expected_slot[@]}" ||
    setup_error "the slot-observation detector rejects the modelled slot occupancy it must accept" \
      "slotBefore: [$slot_full]" \
      "the detectors' own control, not the SC5 Then"
  event_stream_is "$phase_full" "${expected_phase[@]}" ||
    setup_error "the phase-stream detector rejects the ordered client action stream it must accept" \
      "phase: [$phase_full]" \
      "the detectors' own control, not the SC5 Then"
  printf 'SC5 control: accepted the modelled FIFO, LIFO, post-flush, slot-observation and phase streams\n'

  # One identity duplicated in place of another that is missing, the same count either way: a
  # detector reading a count, or a set without regard to a repeat, would accept this.
  duplicated_missing=()
  for e in "${expected_staged[@]}"; do
    [ "$e" = "0" ] && continue
    duplicated_missing+=("$e")
  done
  duplicated_missing+=(256)
  if id_multiset_is "$(bracketed "${duplicated_missing[@]}")" "${expected_staged[@]}"; then
    setup_error "the staged/completed identity detector accepted one identity duplicated and another missing" \
      "staged/delivered: [$(bracketed "${duplicated_missing[@]}")]" \
      "the detectors' own control, not the SC5 Then"
  fi
  printf 'SC5 control: rejected a completed set with 0 missing and 256 duplicated\n'

  # The two identities either side of the capacity crossing exchanged — the 256 the ring served last
  # and the 128 the spill to `inject` served first: every token is still present, so only a detector
  # that reads the *order* of the receipts rejects this.
  swapped=("${expected_fifo[@]}")
  i=128
  tmp="${swapped[$i]}"
  swapped[i]="${swapped[i + 1]}"
  swapped[i + 1]="$tmp"
  if id_sequence_is "$(bracketed "${swapped[@]}")" "${expected_fifo[@]}"; then
    setup_error "the FIFO receipt detector accepted a token-preserving swap across the capacity crossing" \
      "fifo: [$(bracketed "${swapped[@]}")]" \
      "the detectors' own control, not the SC5 Then"
  fi
  printf 'SC5 control: rejected the swapped capacity-crossing pair %s and %s\n' \
    "${expected_fifo[128]}" "${expected_fifo[129]}"

  # The phase boundary: a first-phase `fifo` that carries 300 and 301, which is what a client that
  # staged them before the first batch was drained would record. `Pool.take` serves the ring before
  # `inject`, so those later-phase identities land in the batch's own take receipts ahead of the
  # remaining `inject` work — `0..127,256,300,301,128..253` for the batch's 257 receipts — while the same
  # 263 identities are all still delivered once the drain finishes. Only the phase boundary `fifo`
  # binds rejects this, so the drained multiset alone can never carry the phase claim.
  early_staged=("${expected_fifo[@]:0:129}")
  early_staged+=(300 301)
  early_staged+=("${expected_fifo[@]:129:126}")
  if id_sequence_is "$(bracketed "${early_staged[@]}")" "${expected_fifo[@]}"; then
    setup_error "the FIFO receipt detector accepted 300/301 staged before the first batch was drained" \
      "fifo: [$(bracketed "${early_staged[@]}")]" \
      "the detectors' own control, not the SC5 Then"
  fi
  printf 'SC5 control: rejected a phase-one FIFO carrying %s,%s ahead of the drain\n' "300" "301"

  # The ordered phase stream's own near miss: the same five events, once each, with the two stagings
  # recorded before the `batch-drained` event they must follow, which is what a client that staged
  # `300` and `301` before the drain would record. Every token is still present exactly once, so only
  # a detector reading the stream's order rejects it, and the eventual `staged`/`delivered` sets stay
  # right — the `phase` assertion is what the early stage has to fail.
  early_phase="${expected_phase[2]},${expected_phase[3]},${expected_phase[0]},${expected_phase[1]},${expected_phase[4]}"
  if event_stream_is "$early_phase" "${expected_phase[@]}"; then
    setup_error "the phase-stream detector accepted staging before the first batch was drained" \
      "phase: [$early_phase]" \
      "the detectors' own control, not the SC5 Then"
  fi
  printf 'SC5 control: rejected a token-preserving early-stage phase stream [%s]\n' "$early_phase"

  # A fourth poll of the slot, carrying the identity the flush should have moved to `inject`: the
  # tokens are a superset of the correct sequence, so only the sequence length and order reject it.
  fourth_poll=("${expected_lifo[@]}" 403)
  if id_sequence_is "$(bracketed "${fourth_poll[@]}")" "${expected_lifo[@]}"; then
    setup_error "the LIFO receipt detector accepted a fourth poll instead of the allowance flush" \
      "lifo: [$(bracketed "${fourth_poll[@]}")]" \
      "the detectors' own control, not the SC5 Then"
  fi
  printf 'SC5 control: rejected a LIFO sequence that took %s as a fourth poll\n' "403"

  # An always-empty slot: every slot observation is `-`, the shape a client that recorded no
  # scheduler state — or a detector that merely counted entries — would emit. The populated-slot
  # control above is the affirmative half of the same sequence detector; this near miss is the
  # negative half, without which a vacuous allowance test would pass.
  empty_slot='[-,-,-,-]'
  if id_sequence_is "$empty_slot" "${expected_slot[@]}"; then
    setup_error "the slot-observation detector accepted an always-empty slot" \
      "slotBefore: [$empty_slot]" \
      "the detectors' own control, not the SC5 Then"
  fi
  printf 'SC5 control: rejected an always-empty slot [%s]\n' "$empty_slot"
}

# --- SC5 — the bounded FIFO ring, the LIFO allowance and the overflow keep every staged identity.
check_sc5() {
  local out status line staged phase fifo lifo flush slot delivered remaining
  local -a records=()

  queue_expectation
  check_queue_receipt_detector

  out="$(bounded lake exe controls --executor-queue)"
  status=$?
  check_status SC5 "$status" "lake exe controls --executor-queue"
  require_header "$out"

  mapfile -t records < <(grep '^exec|queue|' <<<"$out" || true)
  [ "${#records[@]}" -eq 1 ] ||
    fail "SC5 Then: queue capacity, LIFO flush or identities missing" \
      "expected exactly one exec|queue| record, saw ${#records[@]}"
  line="${records[0]}"

  record_is "${line#exec|queue|}" staged phase fifo lifo flush slotBefore delivered remaining ||
    fail "SC5 Then: queue capacity, LIFO flush or identities missing" \
      "the record is not exactly staged/phase/fifo/lifo/flush/slotBefore/delivered/remaining with nonempty values: [$line]"

  staged="$(field staged "$line")" ||
    fail "SC5 Then: queue capacity, LIFO flush or identities missing" \
      "no single nonempty staged field: [$line]"
  phase="$(field phase "$line")" ||
    fail "SC5 Then: queue capacity, LIFO flush or identities missing" \
      "no single nonempty phase field: [$line]"
  fifo="$(field fifo "$line")" ||
    fail "SC5 Then: queue capacity, LIFO flush or identities missing" \
      "no single nonempty fifo field: [$line]"
  lifo="$(field lifo "$line")" ||
    fail "SC5 Then: queue capacity, LIFO flush or identities missing" \
      "no single nonempty lifo field: [$line]"
  flush="$(field flush "$line")" ||
    fail "SC5 Then: queue capacity, LIFO flush or identities missing" \
      "no single nonempty flush field: [$line]"
  slot="$(field slotBefore "$line")" ||
    fail "SC5 Then: queue capacity, LIFO flush or identities missing" \
      "no single nonempty slotBefore field: [$line]"
  delivered="$(field delivered "$line")" ||
    fail "SC5 Then: queue capacity, LIFO flush or identities missing" \
      "no single nonempty delivered field: [$line]"
  remaining="$(field remaining "$line")" ||
    fail "SC5 Then: queue capacity, LIFO flush or identities missing" \
      "no single nonempty remaining field: [$line]"

  # The staged and completed identities, each read out of its own named field as a multiset: the
  # 263 identities must be staged once each and completed once each, so a duplicate, a missing
  # identity or an unknown one fails here rather than passing on the count.
  id_multiset_is "$staged" "${expected_staged[@]}" ||
    fail "SC5 Then: queue capacity, LIFO flush or identities missing" \
      "staged=$staged: the staged identities are not the ${#expected_staged[@]} expected ones, each once"
  id_multiset_is "$delivered" "${expected_staged[@]}" ||
    fail "SC5 Then: queue capacity, LIFO flush or identities missing" \
      "delivered=$delivered: the completed identities are not the ${#expected_staged[@]} staged ones, each exactly once"

  # The client's own ordered phase stream, read out of its named field: the first batch drains before
  # the fresh tick, and the two FIFO stagings and the root local spawn follow that drain. A stream
  # that recorded a `stage:300` or `stage:301` before `batch-drained` fails here even though the
  # `staged` and `delivered` sets above still hold all 263 identities and the batch's receipts look
  # right.
  event_stream_is "$phase" "${expected_phase[@]}" ||
    fail "SC5 Then: queue capacity, LIFO flush or identities missing" \
      "phase=$phase: the client's phase events are not the ordered batch-drained,tick-start,stage:300,stage:301,spawn:400"

  # The receipt sequences, each read out of its own named field in order: the capacity crossing of
  # phase one, the allowance's three polls and the flush that follows them in phase two. `fifo` binds
  # the first phase's boundary and `flush` the second's, so a 300/301 staged before the drain fails
  # the `fifo` sequence even though `staged` and `delivered` still hold all 263 identities.
  id_sequence_is "$fifo" "${expected_fifo[@]}" ||
    fail "SC5 Then: queue capacity, LIFO flush or identities missing" \
      "fifo=$fifo: the phase-one ring receipts are not the modelled 0..127 and 256 then 128..255; a 300/301 staged before the drain would appear here"
  id_sequence_is "$lifo" "${expected_lifo[@]}" ||
    fail "SC5 Then: queue capacity, LIFO flush or identities missing" \
      "lifo=$lifo: the slot's take receipts are not the modelled 400,401,402"
  id_sequence_is "$flush" "${expected_flush[@]}" ||
    fail "SC5 Then: queue capacity, LIFO flush or identities missing" \
      "flush=$flush: the post-flush receipts are not the modelled 300,301,403"
  id_sequence_is "$slot" "${expected_slot[@]}" ||
    fail "SC5 Then: queue capacity, LIFO flush or identities missing" \
      "slotBefore=$slot: the scheduler's slot observations are not the modelled 0:400,1:401,2:402,3:403"
  [ "$remaining" = "0" ] ||
    fail "SC5 Then: queue capacity, LIFO flush or identities missing" \
      "remaining=$remaining: the drain left queued work; remaining only corroborates the receipts above"

  printf 'SC5 ok: %d staged identities each delivered once; phase=%s; fifo=%d lifo=%d flush=%d slotBefore=%d receipts in the modelled order; remaining=%s\n' \
    "${#expected_staged[@]}" "$phase" "${#expected_fifo[@]}" "${#expected_lifo[@]}" "${#expected_flush[@]}" "${#expected_slot[@]}" "$remaining"
}

# net_ok <record> — the socket observations of one invocation, as a detector so its own control can reuse it
# rather than a lookalike: one server thread, a client that is not on it, every reply exact, and the pool empty
# after every connection was awaited. `heldBefore` is the control for that last reading — it must be non-zero,
# because the reader is the same one and nothing else in the run shows it can see work.
net_ok() {
  local rec="$1" c st cam ec hb ifa
  c="$(field connections "$rec")" || return 1
  st="$(field serverThreads "$rec")" || return 1
  cam="$(field clientAmongServer "$rec")" || return 1
  ec="$(field echoes "$rec")" || return 1
  hb="$(field heldBefore "$rec")" || return 1
  ifa="$(field inFlightAfter "$rec")" || return 1
  [ "$st" = "1" ] || return 1
  [ "$cam" = "false" ] || return 1
  [ "$ec" = "$c" ] || return 1
  [ "$hb" != "0" ] || return 1
  [ "$ifa" = "0" ] || return 1
}

# --- SC7 — sockets on our carriers: one server thread, a client that is not on it, exact replies ————————————
check_sc7() {
  local out status line ctl connections server_threads client_among echoes held_before in_flight_after
  local ctl_threads_two ctl_threads_repeat ctl_perturbed
  local near
  local -a records=()

  out="$(bounded lake exe controls --runtime-net)"
  status=$?
  check_status SC7 "$status" "lake exe controls --runtime-net"
  require_header "$out"

  mapfile -t records < <(grep '^net|' <<<"$out" || true)
  [ "${#records[@]}" -eq 1 ] ||
    fail "SC7 Then: socket work on the carrier not observed exactly once" \
      "expected exactly one net| record, saw ${#records[@]}"
  line="${records[0]}"

  record_is "${line#net|}" connections serverThreads clientAmongServer echoes heldBefore inFlightAfter wallUs ||
    fail "SC7 Then: socket work on the carrier not observed exactly once" \
      "the record is not exactly connections/serverThreads/clientAmongServer/echoes/heldBefore/inFlightAfter/wallUs with nonempty values: [$line]"

  # The detector's own control, from the record syntax and the expectation alone: it must accept a
  # well-formed record, and reject the four near misses a runtime that ran socket work on another thread,
  # shared the carrier with the client, lost a task or dropped a connection's reply would produce.
  net_ok 'connections=16|serverThreads=1|clientAmongServer=false|echoes=16|heldBefore=3|inFlightAfter=0|wallUs=1' ||
    setup_error "SC7: the socket-observation detector rejected a well-formed record" \
      "the detectors' own control, not the SC7 Then"
  for near in \
    'connections=16|serverThreads=2|clientAmongServer=false|echoes=16|heldBefore=3|inFlightAfter=0|wallUs=1' \
    'connections=16|serverThreads=1|clientAmongServer=true|echoes=16|heldBefore=3|inFlightAfter=0|wallUs=1' \
    'connections=16|serverThreads=1|clientAmongServer=false|echoes=16|heldBefore=3|inFlightAfter=1|wallUs=1' \
    'connections=16|serverThreads=1|clientAmongServer=false|echoes=15|heldBefore=3|inFlightAfter=0|wallUs=1'; do
    if net_ok "$near"; then
      setup_error "SC7: the socket-observation detector accepted a near miss" \
        "record: [$near]" \
        "the detectors' own control, not the SC7 Then"
    fi
  done
  printf 'SC7 control: rejected a second server thread, a carrier shared with the client, a leaked task and a missed reply\n'

  ctl="$(grep '^netctl|' <<<"$out" | head -1)"
  [ -n "$ctl" ] ||
    setup_error "SC7: the detector controls are missing" "no netctl record in the invocation"
  record_is "${ctl#netctl|}" threadsOnTwo threadsOnRepeat perturbed ||
    setup_error "SC7: the detector-control record is not the expected shape" "control: [$ctl]"
  bound_field ctl_threads_two threadsOnTwo "$ctl" "SC7 control"
  bound_field ctl_threads_repeat threadsOnRepeat "$ctl" "SC7 control"
  bound_field ctl_perturbed perturbed "$ctl" "SC7 control"
  [ "$ctl_threads_two" = "2" ] ||
    setup_error "SC7: the distinct-thread detector did not count two on a two-distinct sample" \
      "threadsOnTwo=$ctl_threads_two"
  [ "$ctl_threads_repeat" = "1" ] ||
    setup_error "SC7: the distinct-thread detector did not collapse a repeat" \
      "threadsOnRepeat=$ctl_threads_repeat"
  [ "$ctl_perturbed" = "0" ] ||
    setup_error "SC7: the reply comparison matched a payload with one extra byte" \
      "perturbed=$ctl_perturbed"

  net_ok "${line#net|}" ||
    fail "SC7 Then: socket work was not observed to run on one carrier with every reply exact" \
      "record=[$line]"

  bound_field connections connections "$line" "SC7 Then"
  bound_field server_threads serverThreads "$line" "SC7 Then"
  bound_field client_among clientAmongServer "$line" "SC7 Then"
  bound_field echoes echoes "$line" "SC7 Then"
  bound_field held_before heldBefore "$line" "SC7 Then"
  bound_field in_flight_after inFlightAfter "$line" "SC7 Then"

  printf 'SC7 ok: connections=%s serverThreads=%s clientAmongServer=%s echoes=%s heldBefore=%s inFlightAfter=%s\n' \
    "$connections" "$server_threads" "$client_among" "$echoes" "$held_before" "$in_flight_after"
}

case "${1:-}" in
SC1) check_sc1 ;;
SC2) check_sc2 ;;
SC3) check_sc3 ;;
SC4) check_sc4 ;;
SC5) check_sc5 ;;
SC6) check_sc6 ;;
SC7) check_sc7 ;;
*)
  printf 'usage: bash tests/executor-contract.sh SC1|SC2|SC3|SC4|SC5|SC6|SC7\n' >&2
  exit 2
  ;;
esac
