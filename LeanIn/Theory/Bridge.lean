import Std
import LeanIn.Theory.World

/-!
# The bridge: the only axioms

`World.lean` proves the *model's* properties — mutual exclusion, no notification memory, permitted
spurious wakeups, no fairness. None of that is assumed. What is assumed is the connection between
that model and the running program, and this file is the whole of it.

Everything here is an `axiom`, so `#print axioms` on any theorem downstream will name exactly what it
rests on. Nine of them are operation contracts — creation of a mutex and of a condvar, the three mutex
operations, waiting, the two notifications, and the clock — and they are the TCB (D7), one per native
operation the scheduler uses. One further assumption has
no axiom of its own: that the objects a statement *relates* are not aliased under its representation,
`Rep.NonAliasing`. It is a *definition*, carried as an explicit hypothesis by the theorems that need it
rather than by the operation axioms, because no single operation relates two runtime objects. Every
theorem below says which it is.

## Why axioms, and why only here

Lean gives `IO`/`BaseIO` no semantics (`docs/proof-strategy.md` Gap A), so the statement "running this
operation advances the world like that" cannot be *derived* — it has to be named. `Runs` is that name.
Each axiom then cites the C++ or the standard it claims the runtime honours, so the claim is checkable
by reading rather than taken on faith.

## What is not here

**A6 (thread creation) is absent**, because v1 is single-carrier and spawns no threads. It joins this
file when the multi-carrier scheduler does (D2, D11).

**`IO.Promise` and atomics are absent**, because they are not used (D7).
-/

namespace LeanIn

/-! ### The representation

The mapping from runtime objects to model indices is carried **alongside** the world, not inside it.

It has to be, for a mechanical reason rather than an aesthetic one: a world-indexed claim has to be
re-established after every step, and no axiom did. After any call you no longer knew that `m` was the
lock at `l`, so no *second* call on the same object could be reasoned about -- the seven axioms were
unusable in sequence, which is why nothing downstream consumed them. With the map fixed outside the
world, `IsLock r m l` survives every transition for free and the axioms compose.

It is a **parameter of the interpretation**, not only of the statements that use it, and that is a repair
rather than a tidy-up. With the map outside `Runs`, one witness could be re-instantiated at every
constant representation, so `lock_spec` entailed that acquiring a single mutex sets *every* model lock's
owner to the caller -- `LeanIn/Test/BridgeControls.lean` proves that against the earlier signature, and
the same construction emptied every condvar from one broadcast. An execution is an execution *under a
representation*; two maps are two interpretations, and no witness is shared between them. -/

/-- Which model lock and condvar each runtime object stands for. A function, so its values are as opaque
to Lean as the C++ objects are: nothing here says which index a given `std::mutex` receives. -/
structure Rep where
  lockOf : Std.BaseMutex → LockId
  condOf : Std.Condvar → CondvarId

/-! ### The uninterpreted pieces -/

/-- The interpretation. `Runs r t op w res w'` means: **under representation `r`**, **thread `t`**
executes the `BaseIO` operation `op` in world `w`, terminating with result `res` in world `w'`.

The acting thread is a *parameter* rather than a hypothesis, because the model's steps name their actor
(`Act.lock l t`, `Act.unlock l t`, `Act.wait c l t`) and a bridge that omits it cannot say what any of
them says about a particular thread. Its absence was not cosmetic: with `t` free, A1 and A2 said "the
owner is `some t` for every `t`", which is unsayable about a machine with two threads, and A2's `false`
case had no way to conclude that *the caller* had failed.

**`w'` is the world after *this operation's* effect.** Other threads acting during the call appear as
separate transitions — `Step` is a relation over single actions, and that is where they live. The
alternative reading, "the world when the call returns, including whatever other threads did meanwhile",
is what A1's comment invites when it says "the returned world", and it is *unsound* for any property a
concurrent actor can change: another carrier may acquire a lock after this thread released it and before
the call returns, so a conclusion of the form "the returned world does not hold `l`" would forbid a real
execution. Properties that cannot be taken away — *holding* a lock — hold under either reading; the
ones that can — *not* holding it — hold only under this one. Stated once here, because every axiom below
rests on it.

**For a call with internal stages, this pair is the *composition*, not one instant.** `wait` releases and
enrols, suspends, wakes and re-acquires; A4's conclusion therefore speaks about (holds before, holds after)
rather than about any single one of those stages, and the stages themselves are the model's transitions --
`wait_cycle_reachable` exhibits that path. The distinction matters to anything wanting the *interior* of a
call: one isolated effect and one call interval are different objects, and only the second type-checks
against a `do` block. -/
opaque Runs {α : Type} (r : Rep) (t : Tid) (op : BaseIO α) (w : World) (res : α) (w' : World) : Prop

/-- **A complete call, with its interference named.** `CallExec r t op w res trace w'` means: under
representation `r`, thread `t` invokes the native operation `op` in world `w`, the execution's steps are
`trace`, and it returns `res` in `w'`.

A different object from `Runs`, and the difference is the point rather than a naming preference. `Runs`
relates one **isolated effect**, with no other actor inside it. A call that spans stages — `wait` releases
and enrols, suspends, wakes, re-acquires — is not an isolated effect, and no pair of worlds can be "the
effect with interference removed", because *which* wakeup arrives and *which* thread re-acquires is decided
by the interleaving. So the interference is an **argument** here, not something a reading of `w'` excludes:
`trace` records the caller's own stages and the environment's steps between them.

The correspondence from `trace` to a model path is not established here; that is the next milestone's work,
and this declaration exists so that `wait` is no longer written as though it were an isolated effect. What
a returning `wait` must exhibit in its trace is stated in `wait_spec`. -/
opaque CallExec {α : Type} (r : Rep) (t : Tid) (op : BaseIO α) (w : World) (res : α)
    (trace : List Act) (w' : World) : Prop

/-! ### Reading the map -/

/-- `m` stands for model lock `l` under `r`. A definition rather than an axiom, because it must hold
*stably*: it mentions `r`, never a world. -/
def IsLock (r : Rep) (m : Std.BaseMutex) (l : LockId) : Prop := r.lockOf m = l

/-- `cv` stands for model condvar `c` under `r`. -/
def IsCondvar (r : Rep) (cv : Std.Condvar) (c : CondvarId) : Prop := r.condOf cv = c

/-- **Two runtime mutexes are not aliased under `r`**: they occupy different model locks.

This is the condition the bridge cannot derive and a use must supply. It is deliberately **local**
rather than a global injectivity condition over every `Std.BaseMutex`. The runtime guarantees
distinctness only for objects that are *simultaneously live*, and the allocator may reuse a freed
object's address, so a global injection is an over-assumption that may be impossible to discharge. What
a statement actually needs is that the objects *it* relates are not aliased, which is what this says.

Nothing about a single mutex needs it, which is why the operation axioms below do not carry it; a
theorem relating two represented mutexes must, and `distinct_mutexes_are_distinct_locks` is where the
condition is both required and used. -/
def Rep.NonAliasing (r : Rep) (m₁ m₂ : Std.BaseMutex) : Prop := r.lockOf m₁ ≠ r.lockOf m₂

/-- The same for two condition variables. -/
def Rep.NonAliasingC (r : Rep) (cv₁ cv₂ : Std.Condvar) : Prop := r.condOf cv₁ ≠ r.condOf cv₂

/-! ### A0 — creation

`lean_io_basemutex_new` (`mutex.cpp:20`) and `lean_io_condvar_new` (`mutex.cpp:46`) default-construct a
`std::mutex` and a `std::condition_variable`. They are two of the nine native operations the scheduler
uses, and until now the only ones with no contract at all.

What can be stated is the *state* a fresh object is in. What cannot be stated here is that a fresh
object receives an index no live object already holds. That is *identity*, and stating it needs liveness
and allocation identities in the model: the representation is a fixed map over runtime objects, so it
cannot distinguish one just created from one that has existed all along. Until that exists, identity
non-aliasing stays the explicit local hypothesis `Rep.NonAliasing`, not a consequence of creation. -/

/-- **A0 — mutex creation.** A completed `new` yields an unowned model lock, and leaves the clock
alone. -/
axiom newMutex_spec {r : Rep} {w w' : World} {l : LockId} {t : Tid} {m : Std.BaseMutex} :
    IsLock r m l →
    Runs r t (Std.BaseMutex.new : BaseIO Std.BaseMutex) w m w' →
    (w'.locks l).owner = none ∧ w.SameClock w'

/-- **A0 — condvar creation.** A completed `new` yields a condvar with no waiters, and leaves the clock
alone. -/
axiom newCondvar_spec {r : Rep} {w w' : World} {c : CondvarId} {t : Tid} {cv : Std.Condvar} :
    IsCondvar r cv c →
    Runs r t (Std.Condvar.new : BaseIO Std.Condvar) w cv w' →
    (w'.condvars c).waiters = [] ∧ w.SameClock w'

/-! ### A1–A2 — the mutex -/

/-- **A1 — acquisition.** `lean_io_basemutex_lock` (`mutex.cpp:27`) → `std::mutex::lock`; ISO C++
`[thread.mutex.requirements.mutex]`.

A successful acquisition is observed as ownership of the corresponding model lock. The *blocking*
case is not modelled as a transition: an operation that has not returned has not stepped.

Stated as a property of the returned world rather than an equality with `afterLock w l t`, so that the
world is not forced to be *only* what the model says — the mutex is free to have other effects the
model does not track. -/
axiom lock_spec {r : Rep} {m : Std.BaseMutex} {w w' : World} {l : LockId} {t : Tid} :
    IsLock r m l → Runs r t (Std.BaseMutex.lock m) w () w' →
    (w'.locks l).owner = some t ∧ w.SameClock w'

/-- **A2 — non-blocking acquisition.** `lean_io_basemutex_try_lock` (`mutex.cpp:33`) →
`std::mutex::try_lock`.

`true` means *the caller* acquired; `false` means it did not, and it must not have blocked.

**Preservation is the load-bearing conjunct of the `false` case; the second follows from it.** Ownership
unchanged alone does not say the caller failed: a world in which the caller already held the lock and
`tryLock` returned `false` satisfies it, and that is the case the standard leaves undefined — the A2
control in `Test/Control.lean` says so in as many words. That is why the axiom carries the non-ownership
*precondition* the standard requires, and why the conclusion that the owner is not the caller is kept only
for convenience: it is the precondition rewritten through preservation, not an independent assumption. -/
axiom tryLock_spec {r : Rep} {m : Std.BaseMutex} {w w' : World} {l : LockId} {t : Tid} {b : Bool} :
    IsLock r m l → (w.locks l).owner ≠ some t →
    Runs r t (Std.BaseMutex.tryLock m) w b w' →
    (b = true → (w'.locks l).owner = some t) ∧
    (b = false → (w'.locks l).owner = (w.locks l).owner ∧ (w'.locks l).owner ≠ some t) ∧
    w.SameClock w'

/-- **A3 — release.** `lean_io_basemutex_unlock` (`mutex.cpp:37`) → `std::mutex::unlock`.

Requires ownership — releasing without holding is undefined behaviour, which is why the model has no
transition for it (`unlock_without_ownership_has_no_transition`). -/
axiom unlock_spec {r : Rep} {m : Std.BaseMutex} {w w' : World} {l : LockId} {t : Tid} :
    IsLock r m l → (w.locks l).owner = some t →
    Runs r t (Std.BaseMutex.unlock m) w () w' → (w'.locks l).owner = none ∧ w.SameClock w'

/-! ### A4–A5 — the condition variable -/

/-- **A4 — waiting.** `lean_io_condvar_wait` (`mutex.cpp:55`) → `std::condition_variable::wait`, under
`std::adopt_lock_t`; ISO C++ `[thread.condition.condvar]`.

The runtime call is the *whole* park-and-resume: it releases the mutex, blocks, and re-acquires before
returning. So on return the lock is held again.

**The call spans a path, and the trace is where its stages are named.** To its caller `wait` is one
operation; in the model it is three steps — park (`afterWait` releases the lock and enrols the waiter),
resume, re-acquire — which `World.wait_cycle_reachable` exhibits and `World.afterWait_releases` shows
cannot be collapsed into one, since the model's own `wait` step leaves the lock free. That is why this
hypothesis is `CallExec` and not `Runs`: an endpoint pair cannot say which wakeup arrived or which thread
re-acquired, and `Act.WaitStages tr` says that the stages are there, in order, with environment steps
permitted between them. The correspondence from the trace to a model path is still owed; the stages being
present is the precondition for stating it.

**The clock is deliberately not framed here, and this is not an oversight.** `Runs`'s isolated effects
preserve the clock state, and that is right for a single event. A call interval is not one: another
carrier may `tick` or read the clock between the stages, and requiring equality across the interval would
exclude exactly those executions. The converse mistake is worth naming too — preserving the clock in an
*effect* is not the same claim as the *call* taking no time. Sample evolution across a call belongs to its
trace, and a `SameClock` conjunct here made the two claims identical.

Both conjuncts are what the *caller* observes on return: it holds the lock again, and it has stopped
being a waiter. The second is not decoration. Without it nothing downstream could conclude that a
`wait` had ended, which is the only thing the call is for; and with only the first the axiom is
satisfied by a world in which the caller is still enrolled — a state no machine can be in, since it
returned.

**What the refinement still owes, and where it lives.** The model does not *force* the resumed waiter
to be the thread that re-acquires — `World.reacquisition_is_anyone` shows any thread may take the freed
lock — so a `wait` obligation must carry that linkage explicitly rather than let the matching endpoint
stand in for it. That obligation belongs to the refinement of the scheduler's wake and await paths in
M3, not to the model refinement in M2: M2 closed, and what it delivered was the waiter *list* (enrol and
de-enrolment), not the cycle. -/
axiom wait_spec {r : Rep} {cv : Std.Condvar} {m : Std.BaseMutex} {w w' : World} {c : CondvarId}
    {l : LockId} {t : Tid} {trace : List Act} :
    IsCondvar r cv c → IsLock r m l → (w.locks l).owner = some t →
    CallExec r t (Std.Condvar.wait cv m) w () trace w' →
    (w'.locks l).owner = some t ∧ t ∉ (w'.condvars c).waiters ∧ Act.WaitStages c l t trace

/-- **A5 — notification, and its absence of memory.** `lean_io_condvar_notify_one`
(`mutex.cpp:62`) → `std::condition_variable::notify_one`.

Stated as an **exact** effect on the waiter list, because a count is not an effect. The earlier form —
"does not grow, and loses at most one" — was satisfied by `[Alice, Bob] → [Carol, Dave]`: the length is
unchanged and at most one entry was lost, so a wakeup that *replaced* the waiter set was admissible, and
the model's own `erase` has no such behaviour. What is stated instead: the list is either **untouched**
(nothing was woken, which is the lost notification of A5, proved as `notifyOne_no_waiters` in
`World.lean`) or **exactly one named element is gone**.

`notifyOne_no_additions` is the consequence the count could not give, and `notifyOne_selects` names the
selection guarantee itself.

**The native guarantee is selection, and it is stated; what stays unstated is that the woken thread runs.**
The C++ draft has `notify_one` unblock one thread if any are blocked (`[thread.condition.condvar]`), so the
axiom requires exactly that: an empty list stays empty, and otherwise one named entry is removed. That is
*not* a fairness assumption — unblocking is an event, and the standard does not claim the thread is then
scheduled, acquires the mutex, or returns from `wait`. Those are progress, they remain unstated, and the
later rungs are where they belong. The distinction matters enough to have been got wrong here: an earlier
version of this comment called the selection guarantee a fairness assumption and weakened the axiom to
match it, which is the wrong repair of the right observation. -/
axiom notifyOne_spec {r : Rep} {cv : Std.Condvar} {w w' : World} {c : CondvarId} {t : Tid} :
    IsCondvar r cv c → Runs r t (Std.Condvar.notifyOne cv) w () w' →
    w.SameClock w' ∧
    (((w.condvars c).waiters = [] ∧ (w'.condvars c).waiters = []) ∨
     ∃ front : List Tid, ∃ x : Tid, ∃ back : List Tid,
       (w.condvars c).waiters = front ++ x :: back ∧
       (w'.condvars c).waiters = front ++ back)

/-- **A5 — broadcast.** `lean_io_condvar_notify_all` (`mutex.cpp:67`).

Every thread waiting is released — it moves to *blocked on the mutex* rather than on the condition
variable — so every waiter present at the call is gone, and **no waiter appears**. Both directions are
needed: "every waiter present is gone" plus "does not grow" was still satisfied by `[Alice, Bob] →
[Carol, Dave]`, since the length is unchanged and every original member did disappear. The second clause
is what makes the effect exact rather than merely a bound, and `notifyAll_no_additions` is its
consequence.

This is what the shutdown path relies on, and it is why the axiom is not the same proposition as
`notifyOne_spec`: a bare "does not grow" clause admits a `notifyAll` that releases nobody, leaving the
shutdown argument proved of the model and never carried across the bridge.

Nothing beyond removal is claimed, and removal itself is *forced* rather than permitted: the two clauses
together leave the list empty whenever it was non-empty. What is not claimed is that any of those threads
runs, reacquires the mutex, or returns — that is progress, and progress is outside the base bridge. -/
axiom notifyAll_spec {r : Rep} {cv : Std.Condvar} {w w' : World} {c : CondvarId} {t : Tid} :
    IsCondvar r cv c → Runs r t (Std.Condvar.notifyAll cv) w () w' →
    w.SameClock w' ∧
    (∀ u, u ∈ (w.condvars c).waiters → u ∉ (w'.condvars c).waiters) ∧
    (∀ u, u ∈ (w'.condvars c).waiters → u ∈ (w.condvars c).waiters)

/-! ### A7 — the clock -/

/-- **A7 — monotone time.** `lean_io_mono_nanos_now` (`object.cpp:421`).

Three conjuncts, and the third is the one that was missing. Reading the clock does not move model time;
the reading is recorded as the last sample; and it is never behind that previous sample. The first keeps
reads side-effect-free. The second and third together are what make *successive* readings comparable,
and therefore what makes a budget meaningful — without the second, two readings were related only to a
clock that no read moved, and "the clock never goes backwards" stayed a property of the runtime that no
theorem could use. Equal readings are permitted: the native clock has finite resolution. -/
axiom clock_spec {w w' : World} {n : Nat} {t : Tid} :
    Runs r t (IO.monoNanosNow : BaseIO Nat) w n w' →
    w'.clock = w.clock ∧ w'.lastSample = some n ∧ ∀ s, w.lastSample = some s → s ≤ n


/-! ### Composition

The point of carrying the representation outside the world: calls on the same objects can be reasoned
about in sequence. Before, no axiom's conclusion re-established `IsLock`, so after a first call the
representation was lost and no second call on that object could be stated at all — which is why nothing
downstream consumed the axioms.

It is a regression guard as much as a demonstration: make the representation world-indexed again and
it stops compiling.

It needs no non-aliasing condition, and that is worth stating rather than leaving to be noticed: the
mutex index `l` and the condvar index `c` index *different* maps of `World`, so a coincidence between
the two numbers denotes nothing shared. Only two objects of the *same* kind can be aliased. -/
theorem lock_wait_unlock_postcondition {r : Rep} {cv : Std.Condvar} {m : Std.BaseMutex} {c : CondvarId} {l : LockId}
    {t : Tid} {w₁ w₂ w₃ w₄ : World} {trace : List Act}
    (hL : IsLock r m l) (hC : IsCondvar r cv c)
    (h₁ : Runs r t (Std.BaseMutex.lock m) w₁ () w₂)
    (h₂ : CallExec r t (Std.Condvar.wait cv m) w₂ () trace w₃)
    (h₃ : Runs r t (Std.BaseMutex.unlock m) w₃ () w₄) :
    (w₄.locks l).owner = none :=
  (unlock_spec hL (wait_spec hC hL (lock_spec hL h₁).1 h₂).1 h₃).1

/-- **Where non-aliasing is actually required, and used.**

Two distinct runtime mutexes are two model locks, and nothing else in this file can conclude that. The
operation axioms each speak about one object, so none of them needs the condition; a statement relating
two of them must supply it, and that is this theorem.

Without it, a use can hold two independent runtime mutexes whose shared model lock reports a single
owner: the correspondence failing, not the model being wrong. Substituting an uninterpreted predicate
for this condition does not help — it names the requirement and entails nothing, so the aliasing
instantiation stays admissible. -/
theorem distinct_mutexes_are_distinct_locks {r : Rep} {m₁ m₂ : Std.BaseMutex} {l₁ l₂ : LockId}
    (hna : r.NonAliasing m₁ m₂) (h₁ : IsLock r m₁ l₁) (h₂ : IsLock r m₂ l₂) : l₁ ≠ l₂ := by
  intro hEq
  apply hna
  have h₁' : r.lockOf m₁ = l₁ := h₁
  have h₂' : r.lockOf m₂ = l₂ := h₂
  rw [h₁', hEq, ← h₂']


/-- **A reading before and a reading after another bridge call are comparable.**

This is what the clock sample is for, and it is the property that was *not* derivable before the
non-clock operations were required to preserve the clock state. With only adjacent readings related, a
budget with any mutex, condvar or lock call between its start and end readings could conclude nothing:
the intervening axiom was free to reset the sample, and the second reading's bound was vacuous. -/
theorem readings_monotone_across_a_call {r : Rep} {m : Std.BaseMutex} {l : LockId} {t : Tid}
    {w₁ w₂ w₃ w₄ : World} {n₁ n₂ : Nat}
    (hL : IsLock r m l)
    (h₁ : Runs r t (IO.monoNanosNow : BaseIO Nat) w₁ n₁ w₂)
    (h₂ : Runs r t (Std.BaseMutex.lock m) w₂ () w₃)
    (h₃ : Runs r t (IO.monoNanosNow : BaseIO Nat) w₃ n₂ w₄) :
    n₁ ≤ n₂ := by
  have hs : w₂.lastSample = some n₁ := (clock_spec h₁).2.1
  have hpres : w₃.lastSample = w₂.lastSample := by
    have := (lock_spec hL h₂).2
    simp [World.SameClock] at this
    exact this.2
  have hbound : ∀ s, w₃.lastSample = some s → s ≤ n₂ := (clock_spec h₃).2.2
  exact hbound n₁ (by rw [hpres, hs])


/-! ### What the exact notification buys

Two consequences of the exact forms above, and the reason they are stated exactly rather than as counts.
Neither is derivable from "does not grow, and loses at most one", because `[Alice, Bob] -> [Carol, Dave]`
satisfies that and trades one waiter's identity for another. -/

/-- **A notification cannot manufacture a waiter.** -/
theorem notifyOne_no_additions {r : Rep} {cv : Std.Condvar} {w w' : World} {c : CondvarId} {t : Tid}
    (hC : IsCondvar r cv c) (h : Runs r t (Std.Condvar.notifyOne cv) w () w') :
    ∀ u, u ∈ (w'.condvars c).waiters → u ∈ (w.condvars c).waiters := by
  obtain ⟨-, hcase⟩ := notifyOne_spec hC h
  intro u hu
  rcases hcase with ⟨-, hsame⟩ | ⟨front, x, back, hw, hw'⟩
  · exact absurd hu (by simp [hsame])
  · rw [hw'] at hu
    rcases List.mem_append.mp hu with hf | hb
    · rw [hw]; exact List.mem_append.mpr (Or.inl hf)
    · rw [hw]; exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem x hb))

/-- **A broadcast cannot manufacture a waiter either** - it removes every waiter present and adds none,
where "every waiter is gone" together with "does not grow" would have admitted the same replacement. -/
theorem notifyAll_no_additions {r : Rep} {cv : Std.Condvar} {w w' : World} {c : CondvarId} {t : Tid}
    (hC : IsCondvar r cv c) (h : Runs r t (Std.Condvar.notifyAll cv) w () w') :
    ∀ u, u ∈ (w'.condvars c).waiters → u ∈ (w.condvars c).waiters :=
  (notifyAll_spec hC h).2.2

/-- The form the two now-replaced axioms used: "does not grow, and loses at most one". Kept as the control
for the theorems above -- a detector that *matches* the defect while it is present is the only thing that
makes its later absence mean anything. -/
def CountedNotify (before after : List Tid) : Prop :=
  after.length ≤ before.length ∧ before.length ≤ after.length + 1

/-- The old form accepts exactly the replacement the new one refuses, so the strengthening is not a
rephrasing: with two waiters and two *different* waiters after, the count is unchanged and one entry was
lost, and both clauses hold. -/
theorem counted_notify_admits_replacement : CountedNotify [0, 1] [2, 3] := ⟨by decide, by decide⟩

/-- The exact form refuses it: a list that has had one element removed is a sublist of the original, so
`[2, 3]` cannot be the result of removing an element from `[0, 1]`. -/
theorem exact_notify_rejects_replacement :
    ¬ (∃ front : List Tid, ∃ x : Tid, ∃ back : List Tid,
        ([0, 1] : List Tid) = front ++ x :: back ∧ ([2, 3] : List Tid) = front ++ back) := by
  rintro ⟨front, x, back, hw, hw'⟩
  -- the original has one element more than the list it is compared against
  have h1 := congrArg List.length hw
  have h2 := congrArg List.length hw'
  simp [List.length_append, List.length_cons] at h1 h2
  omega

/-- **The selection guarantee, named.** When the waiter list is non-empty the native call unblocks one of
them, so the exact effect is a removal that *must* happen, not one that merely may. -/
theorem notifyOne_selects {r : Rep} {cv : Std.Condvar} {w w' : World} {c : CondvarId} {t : Tid}
    (hC : IsCondvar r cv c) (h : Runs r t (Std.Condvar.notifyOne cv) w () w')
    (hne : (w.condvars c).waiters ≠ []) :
    (w'.condvars c).waiters.length + 1 = (w.condvars c).waiters.length := by
  obtain ⟨-, hcase⟩ := notifyOne_spec hC h
  rcases hcase with ⟨hempty, -⟩ | ⟨front, x, back, hw, hw'⟩
  · exact absurd hempty hne
  · rw [hw, hw', List.length_append, List.length_append, List.length_cons]
    omega

/-! ### The audit

`#print axioms` is the TCB check from `PLAN.md` §6. Two lists, read in opposite directions:

* the `World.lean` theorems below should name **nothing** -- the model's properties are proved, not assumed;
* the bridge theorems should name the bridge axioms -- that is the evidence that they *consume* them, and it
  is what printing only the model's theorems cannot show.

`#print axioms` reports a theorem's *dependencies*, not its **hypotheses**: a lemma carrying `NonAliasing`,
`IsLock` or `IsCondvar` prints the same axiom list either way, because premises are invisible to it. An
axiom-free line below is therefore a statement about what is assumed *as an axiom*, and not about what is
still assumed. The nine named axioms are also not the whole native TCB -- the compiler and runtime sit
outside them -- and none of them says anything about a *runtime-facing* theorem until one exists. -/

#print axioms LeanIn.notifyOne_no_waiters
#print axioms LeanIn.reacquisition_while_others_wait
#print axioms LeanIn.wait_cycle_reachable
#print axioms LeanIn.afterWait_releases
#print axioms LeanIn.reacquisition_is_anyone

#print axioms LeanIn.lock_wait_unlock_postcondition
#print axioms LeanIn.readings_monotone_across_a_call
#print axioms LeanIn.distinct_mutexes_are_distinct_locks
#print axioms LeanIn.notifyOne_no_additions
#print axioms LeanIn.notifyAll_no_additions

end LeanIn
