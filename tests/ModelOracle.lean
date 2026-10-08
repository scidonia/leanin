import LeanIn.Model.Pool
import LeanIn.Model.Scheduler

/-!
# The pure-model oracle for a scripted executor trace

The independent side of `tests/executor-contract.md`'s refinement check. It runs the *fixed script*
below against the pure model — `LeanIn.Model.Pool` for the work bookkeeping and
`LeanIn.Model.Scheduler` for the wake protocol — and prints one canonical record per step:

```
model|trace|op=<name>|pos=<n>|task=<identity>|out=<outcome>
```

The records are computed by the model's own functions, never written out as an expected text, so a
run that matches the executor's `exec|trace|` records is evidence that the executor's transactions
agree with the model, not that two copies of a fixture agree with each other.

## The projection

Every step is one *modelled transaction*, not a change to one model at a time. A submit and an
external enqueue advance `Pool.submit` **and** `Sched.enqueue`; a take that returns a task advances
`Pool.take` **and** `Sched.take`; a take that finds nothing advances neither. `Sched.work` and
`Pool.inFlight` are then the same quantity — the number of items held somewhere — so the two sides of
a comparison refer to the same work rather than to two independent counters, and the two parks in the
script mean what they say: refused while two items are held, granted once both have been taken.

`step` checks that relation after every step and reports a broken projection as a defect of this
fixture (a nonzero exit and a stderr message) rather than as a comparison result, because a trace
from a misaligned projection would be no evidence either way.

The script is shared with the executor: both advance the same ordered operations at the same
positions over the same task identities, so the records are comparable pairwise.
-/

namespace ModelOracle

open LeanIn Model

/-- One step of the fixed script. -/
inductive Op where
  /-- Submit a computation under the given task identity. -/
  | submit (task : Nat)
  /-- An external event delivers a computation under the given task identity. -/
  | enqueue (task : Nat)
  /-- The carrier takes the next item of work. -/
  | take
  /-- The carrier tries to park. -/
  | park

/-- The fixed script: nine ordered operations, at positions 0 to 8.

Position 2 parks while two items are held and is refused; positions 3 and 4 take them; position 5
parks again and is granted; position 6 is the external delivery that unparks the carrier; positions 7
and 8 take that delivery and then find nothing. -/
def script : List Op :=
  [ .submit 0, .submit 1, .park, .take, .take, .park, .enqueue 2, .take, .take ]

/-- The number of steps the script must contain. A shorter script would quietly weaken the
comparison by giving the executor fewer records to match, so the length is checked rather than
assumed. -/
def scriptSteps : Nat := 9

/-- The state a run advances: the pool's work bookkeeping beside the scheduler's wake protocol. -/
structure State where
  /-- The pool's FIFO ring, LIFO slot and inject queue. -/
  pool  : Pool Nat := emptyPool Nat
  /-- The wake protocol, over one carrier. -/
  sched : Sched := Sched.initial 1

/-- A fresh run: an empty pool and a single carrier that holds nothing and is parked nowhere. -/
def initialState : State := { pool := emptyPool Nat, sched := Sched.initial 1 }

/-- One canonical operation record: operation, input position, task identity, returned outcome. -/
def record (op : String) (pos : Nat) (task : String) (out : String) : String :=
  s!"op={op}|pos={pos}|task={task}|out={out}"

/-- The projection relation every step must preserve: the scheduler's work count and the pool's held
work are the same quantity. -/
def State.aligned (st : State) : Bool := st.sched.work == st.pool.inFlight

/-- The broken projection, if any, as the text this fixture reports it with. -/
def alignError (st : State) : Option String :=
  if st.aligned then none
  else some s!"Sched.work={st.sched.work} but Pool.inFlight={st.pool.inFlight}"

/-- Accept a step's result, or reject it when the projection no longer relates the two models. -/
def checked (st : State) (op : String) (pos : Nat) (rec : String) : Except String (State × String) :=
  match alignError st with
  | none   => .ok (st, rec)
  | some e => .error s!"{op} at pos {pos}: {e}"

/-- Advance one step: one modelled transaction, its canonical record, and the projection check. -/
def step (st : State) (o : Op) (pos : Nat) : Except String (State × String) :=
  match o with
  | .submit t =>
    let p := st.pool.submit t
    checked { pool := p, sched := st.sched.enqueue } "submit" pos
      (record "submit" pos (toString t) s!"inflight{p.inFlight}")
  | .enqueue t =>
    let p := st.pool.submit t
    checked { pool := p, sched := st.sched.enqueue } "enqueue" pos
      (record "enqueue" pos (toString t) s!"inflight{p.inFlight}")
  | .take =>
    let taken := st.pool.take
    match taken.1 with
    | some t =>
      match st.sched.take with
      | some s =>
        checked { pool := taken.2, sched := s } "take" pos
          (record "take" pos (toString t) s!"taken{taken.2.taken}")
      | none =>
        .error s!"take at pos {pos}: the pool returned task {t} but the scheduler removed no work"
    | none =>
      match st.sched.take with
      | some _ =>
        .error s!"take at pos {pos}: the pool returned nothing but the scheduler removed work"
      | none =>
        checked { pool := taken.2, sched := st.sched } "take" pos (record "take" pos "-" "none")
  | .park =>
    match st.sched.park with
    | some s =>
      checked { pool := st.pool, sched := s } "park" pos (record "park" pos "-" s!"parked{s.parked}")
    | none =>
      checked st "park" pos (record "park" pos "-" "none")

/-- The scripted run: every state after its step, paired with the record that step produced. -/
def runSteps : State → Nat → List Op → Except String (List (State × String))
  | _, _, [] => .ok []
  | st, pos, o :: rest =>
    match step st o pos with
    | .error e => .error e
    | .ok (st', r) =>
      match runSteps st' (pos + 1) rest with
      | .error e => .error e
      | .ok more => .ok ((st', r) :: more)

/-- The states and records the fixed script produces, in order. -/
def run : Except String (List (State × String)) := runSteps initialState 0 script

end ModelOracle

open ModelOracle

/-- Print one `model|trace|` line per record.

A broken projection or a script of the wrong length is a defect of this fixture rather than a
comparison result, so each is reported on stderr and exits nonzero. -/
def main : IO UInt32 := do
  match run with
  | .error e =>
    IO.eprintln s!"model oracle: the scripted projection is not aligned: {e}"
    return 2
  | .ok steps =>
    if steps.length != scriptSteps then
      IO.eprintln s!"model oracle: the script produced {steps.length} records, expected {scriptSteps}"
      return 2
    for s in steps do
      IO.println s!"model|trace|{s.2}"
    return 0
