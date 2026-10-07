import Std

/-!
# O3 spike — is `Task` usable as a waker?

The one unverified design assumption behind D3 in `docs/decisions.md`:

> an external event attaches a continuation that pushes into a `LeanIn` queue and
> notifies; our task bodies are never `Task`s, so they never run on the stock pool.

This is scaffolding, not the library. The inbox exists only so the spike has
somewhere to push; what is under test is the *seam*.

Two things are observed, and the program checks the first rather than leaving it
to the reader:

1. the thread that runs the waker (the `Task` continuation) and the thread that
   runs the carrier are **different** threads;
2. the carrier is not one of the stock pool's workers.

Incidental finding worth keeping: `IO.println` is `IO Unit`, so it is **not**
available inside a `bindTask` continuation, whose type is `BaseIO (Task β)`.
That is why the waker's identity travels as data rather than being printed where
it is learned.
-/

namespace WakerSpike

structure Event where
  label : String
  tid   : UInt64

structure State where
  items      : List Event := []
  stopping   : Bool := false
  wakerTid   : Option UInt64 := none
  carrierTid : Option UInt64 := none

def newInbox : IO (Std.Mutex State × Std.Condvar) :=
  return (← Std.Mutex.new ({} : State), ← Std.Condvar.new)

/-- Push, notifying under the same lock — the no-lost-wakeup discipline that A5 forces. -/
def inboxPush (inbox : Std.Mutex State) (cv : Std.Condvar) (e : Event) : BaseIO Unit := do
  inbox.atomically do
    let s ← get
    set { s with items := s.items ++ [e] }
    cv.notifyOne

/-- Take, parking until an item arrives or the inbox is stopping. -/
def inboxTake (inbox : Std.Mutex State) (cv : Std.Condvar) : IO (Option Event) :=
  inbox.atomicallyOnce cv
    (pred := do let s ← get; return !s.items.isEmpty || s.stopping)
    (k := do
      let s ← get
      match s.items with
      | []        => return none
      | e :: rest => set { s with items := rest }; return (some e))

def inboxStop (inbox : Std.Mutex State) (cv : Std.Condvar) : IO Unit := do
  inbox.atomically do
    let s ← get
    set { s with stopping := true }
    cv.notifyAll

/-- The carrier: a dedicated OS thread draining the inbox. -/
def carrier (inbox : Std.Mutex State) (cv : Std.Condvar) : IO Unit := do
  let tid ← IO.getTID
  IO.println s!"  carrier  tid={tid}  started"
  inbox.atomically do
    let s ← get
    set { s with carrierTid := some tid }
  let mut go := true
  while go do
    match ← inboxTake inbox cv with
    | some e => IO.println s!"  carrier  tid={← IO.getTID}  consumed \"{e.label}\" (waker tid={e.tid})"
    | none   => go := false
  IO.println s!"  carrier  tid={← IO.getTID}  exiting"

/-- Distinct thread ids the stock pool uses, sampled by spawning trivial tasks. -/
def poolTids (n : Nat) : IO (List UInt64) := do
  let tasks ← (List.range n).mapM (fun _ => IO.asTask (IO.getTID) Task.Priority.default)
  let res ← tasks.mapM (fun t => IO.wait t)
  let mut acc : List UInt64 := []
  for r in res do
    match r with
    | .ok tid => if !acc.contains tid then acc := acc ++ [tid]
    | .error _ => pure ()
  return acc

end WakerSpike

open WakerSpike

def main : IO UInt32 := do
  IO.println s!"  main     tid={← IO.getTID}"

  let (inbox, cv) ← newInbox
  let carrierTask ← IO.asTask (carrier inbox cv) Task.Priority.dedicated

  -- An external event: something the stock runtime owns, completing on the pool.
  let ext ← IO.asTask (do IO.sleep 200; return (7 : Nat)) Task.Priority.default

  -- The seam: hook the completion and route it into our inbox. No printing here —
  -- `IO.println` is unavailable in `BaseIO` — so the waker's tid travels as data.
  let hooked ← BaseIO.bindTask ext (fun v => do
    let tid ← IO.getTID
    inbox.atomically do
      let s ← get
      set { s with wakerTid := some tid }
    inboxPush inbox cv { label := s!"event:{v}", tid := tid }
    return Task.pure ())
  let _ ← IO.wait hooked

  IO.sleep 200
  inboxStop inbox cv
  match ← IO.wait carrierTask with
  | .ok _    => IO.println "  carrier  joined"
  | .error e => IO.println s!"  carrier  errored: {e}"

  let st ← inbox.atomically (return (← get))
  let sampled ← poolTids 32
  IO.println s!"  pool tids sampled: {sampled}"
  match st.wakerTid, st.carrierTid with
  | some w, some c =>
      IO.println s!"  waker tid={w}   carrier tid={c}"
      IO.println s!"  CHECK distinct threads (the seam) : {w != c}"
      IO.println s!"  CHECK carrier not a pool worker  : {!sampled.contains c}"
      IO.println s!"  CHECK waker was a pool worker    : {sampled.contains w}"
  | _, _ => IO.println "  INCONCLUSIVE: waker or carrier never recorded its tid"
  return 0
