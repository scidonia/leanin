import LeanIn.Theory.World

/-!
# Reachability of the model's states

The contracts in `Bridge.lean` cannot be executed: they are propositions about an `opaque` relation, so
no test observes their dynamics. Two things *can* be observed, and this is one of them — `World` is an
executable state machine, so the states the contracts speak about can be enumerated and asked for.

The question this answers is **non-vacuity**. A contract whose hypothesis no reachable state satisfies
is true of nothing, and a comment claiming otherwise would be unfalsifiable. For each hypothesis below
the search runs bounded action sequences and reports the shortest one that reaches it, or that it did
not reach it within the bound. Where the subject of a claim is a *path* rather than a state — the
park/resume cycle — the search reports the sequence and what it passes through.

Nothing here tests the primitives. `lake exe controls` does that, and the two together are the whole of
what can be observed directly: the model's dynamics here, the runtime's there, and the correspondence
between them assumed, per operation, in `Bridge.lean`.

A witness is only convincing if a reader can follow it, so the search is deliberately small: one lock,
one condvar, two threads, four actions.
-/

namespace LeanIn.Test

/-- The actions available to a search, over one lock and one condvar, for the given threads. -/
def actions (tids : List Nat) : List Act :=
  tids.map (Act.lock 0) ++ tids.map (Act.unlock 0) ++ tids.map (fun t => Act.wait 0 0 t) ++
  tids.map (fun t => Act.spurious 0 t) ++ tids.map (fun t => Act.notifyOne 0 t) ++
  [Act.notifyAll 0, Act.tick]

/-- All action sequences of exactly length `n`. -/
def seqs (as : List Act) : Nat → List (List Act)
  | 0 => [[]]
  | n + 1 => (seqs as n).flatMap fun s => as.map fun a => s ++ [a]

/-- The states a sequence passes through from `w`. Stops at the first action whose precondition fails,
so a sequence that is not realisable from `w` reports only the prefix that is. -/
def walk (w : World) : List Act → List World
  | [] => [w]
  | a :: rest => match step w a with
    | none => []
    | some w' => w :: walk w' rest

/-- The shortest sequence, of at most `n` actions from the initial world, satisfying `p` — given both
the sequence and the states it passed through, since some claims are about the path. -/
def witness (tids : List Nat) (n : Nat) (p : List Act → List World → Bool) : Option (List Act) :=
  ((List.range (n + 1)).map (seqs (actions tids))).flatten.findSome? fun s =>
    if p s (walk (default : World) s) then some s else none

/-- One action, for a readable witness. -/
def showAct : Act → String
  | .lock l t     => s!"lock {l} by {t}"
  | .unlock l t   => s!"unlock {l} by {t}"
  | .wait _ l t   => s!"wait {l} by {t}"
  | .notifyOne _ t => s!"notifyOne {t}"
  | .notifyAll _  => "notifyAll"
  | .spurious _ t => s!"spurious {t}"
  | .tick         => "tick"

def showSeq (s : List Act) : String :=
  if s.isEmpty then "(nothing — the initial world already satisfies it)"
  else String.intercalate " → " (s.map showAct)

/-- Report whether a state predicate is reachable, and by what. -/
def check (name : String) (p : World → Bool) (tids : List Nat) (n : Nat) : IO Unit := do
  match witness tids n (fun _ ws => ws.any p) with
  | some s => IO.println s!"  reachable      {name}\n                   by: {showSeq s}"
  | none   => IO.println s!"  NOT REACHED    {name}   (within {n} actions)"

/-- Report whether a claim about a whole path is realisable, and by what. -/
def checkPath (name : String) (p : List Act → List World → Bool) (tids : List Nat) (n : Nat) : IO Unit := do
  match witness tids n p with
  | some s => IO.println s!"  realisable     {name}\n                   by: {showSeq s}"
  | none   => IO.println s!"  NOT REALISED   {name}   (within {n} actions)"

/-- The threads that park anywhere in the sequence. -/
def parkedThreads (s : List Act) : List Nat :=
  s.filterMap fun a => match a with | .wait _ _ t => some t | _ => none

/-- **The park/resume cycle, for one thread.**

`t` parks — and the state right after that step has the lock free and `t` enrolled, which is
`afterWait_releases` — and the sequence ends with `t` holding the lock again and no longer enrolled.

Three versions of this predicate were wrong, and each was caught by running it rather than by reading
it — which is the point of having an executable instrument:

1. The first asked only that the end state have *thread 0* holding the lock and thread 0 not enrolled.
   The witness was `lock 1, wait 1, lock 0`: thread 1 parks and thread *0* takes the lock, and 0 was
   never a waiter. A predicate one thread's acquisition satisfies is not another thread's cycle.
2. The second required the same thread at both ends, but the search then reported nothing at all —
   because the walker dropped the world preceding each action, so every path check was aligned against
   the wrong successor state.
3. The third, with the walker fixed, accepted `lock 0, wait 0, lock 0, spurious 0`: the resume arrived
   *after* the re-acquisition. A `wait` call resumes first and re-acquires second, so the order is part
   of the claim, not an implementation detail.

It now requires all four: the same thread parks; the park's successor state is lock-free with that
thread enrolled; the de-enrolment precedes the final acquisition; and the sequence ends with that
thread holding the lock and not enrolled. -/
def parkResumeCycle (s : List Act) (ws : List World) : Bool :=
  (parkedThreads s).any fun t =>
    -- the park: `t` releases the lock and is enrolled in the state that follows the step
    (s.zip ws.tail).any (fun p =>
      (match p.1 with | .wait _ _ t' => t' == t | _ => false) &&
      (p.2.locks 0).owner == none && (p.2.condvars 0).waiters.contains t) &&
    -- the last action is `t` acquiring the lock, and `t` holds it at the end
    (match s.getLast?, ws.getLast? with
     | some a, some w =>
        (match a with | .lock _ t' => t' == t | _ => false) &&
        (w.locks 0).owner == some t &&
        -- and `t` was already de-enrolled *before* that acquisition: the resume precedes the
        -- re-acquisition, which is what a `wait` call does and what the model path shows
        (match ws.dropLast.getLast? with
         | some w' => !(w'.condvars 0).waiters.contains t
         | none => false)
     | _, _ => false)

def main : IO UInt32 := do
  let tids := [0, 1]
  let n := 4
  IO.println s!"model dynamics — one lock, one condvar, threads {tids}, sequences of at most {n} actions"
  IO.println ""
  IO.println "  hypotheses of the contracts. Each must be reachable, or the contract is true of nothing."
  check "A0/A1  a lock is unowned (the state a fresh lock is in)" (fun w => (w.locks 0).owner == none) tids n
  check "A2/A3/A4  a thread owns the lock" (fun w => (w.locks 0).owner != none) tids n
  check "A5  a thread is enrolled on the condvar" (fun w => !(w.condvars 0).waiters.isEmpty) tids n
  check "A7  model time has advanced" (fun w => w.clock > 0) tids n
  IO.println ""
  IO.println "  and the model's own vacuity controls, in executable form"
  check "an empty waiter set is reachable, as `notifyOne_no_waiters` assumes"
    (fun w => (w.condvars 0).waiters.isEmpty) tids n
  check "and so is a non-empty one, so that control is not a marker matching nothing"
    (fun w => !(w.condvars 0).waiters.isEmpty) tids n
  IO.println ""
  IO.println "  the invariant the waiter model needs: a thread cannot be enrolled twice"
  check "VIOLATION reachable: a thread enrolled twice on one condvar (no machine state)"
    (fun w => (w.condvars 0).waiters.length != (w.condvars 0).waiters.eraseDups.length) tids n
  IO.println ""
  IO.println "  the park/resume cycle, which is a path and not a single state"
  IO.println "  (parks, releases the lock, takes it again, and is no longer enrolled)"
  checkPath "the cycle a runtime `wait` spans (same thread, released at the park)"
    parkResumeCycle tids n
  IO.println ""
  IO.println "  Not testable here: the contracts themselves. They quantify over an `opaque` relation, so"
  IO.println "  their dynamics are not observable; `lake exe controls` observes the primitives instead."
  return 0

end LeanIn.Test
