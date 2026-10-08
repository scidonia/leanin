import Std
import LeanIn.Theory.World

/-!
# The bridge: the only axioms

`World.lean` proves the *model's* properties — mutual exclusion, no notification memory, permitted
spurious wakeups, no fairness. None of that is assumed. What is assumed is the connection between
that model and the running program, and this file is the whole of it.

Everything here is an `axiom`, so `#print axioms` on any theorem downstream will name exactly what it
rests on. Seven of them are operation contracts, and they are the TCB (D7). One further assumption has
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

/-! ### The uninterpreted pieces -/

/-- The interpretation. `Runs t op w r w'` means: **thread `t`** executes the `BaseIO` operation
`op` in world `w`, terminating with result `r` in world `w'`.

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
rests on it. -/
opaque Runs {α : Type} (t : Tid) (op : BaseIO α) (w : World) (r : α) (w' : World) : Prop

/-! ### The representation

The mapping from runtime objects to model indices is carried **alongside** the world, not inside it.

It has to be, for a mechanical reason rather than an aesthetic one: a world-indexed claim has to be
re-established after every step, and no axiom did. After any call you no longer knew that `m` was the
lock at `l`, so no *second* call on the same object could be reasoned about — the seven axioms were
unusable in sequence, which is why nothing downstream consumed them. With the map fixed outside the
world, `IsLock r m l` survives every transition for free and the axioms compose. -/

/-- Which model lock and condvar each runtime object stands for. A function, so its values are as opaque
to Lean as the C++ objects are: nothing here says which index a given `std::mutex` receives. -/
structure Rep where
  lockOf : Std.BaseMutex → LockId
  condOf : Std.Condvar → CondvarId

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

/-! ### A1–A2 — the mutex -/

/-- **A1 — acquisition.** `lean_io_basemutex_lock` (`mutex.cpp:27`) → `std::mutex::lock`; ISO C++
`[thread.mutex.requirements.mutex]`.

A successful acquisition is observed as ownership of the corresponding model lock. The *blocking*
case is not modelled as a transition: an operation that has not returned has not stepped.

Stated as a property of the returned world rather than an equality with `afterLock w l t`, so that the
world is not forced to be *only* what the model says — the mutex is free to have other effects the
model does not track. -/
axiom lock_spec {r : Rep} {m : Std.BaseMutex} {w w' : World} {l : LockId} {t : Tid} :
    IsLock r m l → Runs t (Std.BaseMutex.lock m) w () w' →
    (w'.locks l).owner = some t ∧ w.SameClock w'

/-- **A2 — non-blocking acquisition.** `lean_io_basemutex_try_lock` (`mutex.cpp:33`) →
`std::mutex::try_lock`.

`true` means *the caller* acquired; `false` means it did not, and it must not have blocked.

**Both conjuncts of the `false` case are load-bearing, and preservation is the weaker one.** Ownership
unchanged alone does not say the caller failed: a world in which the caller already held the lock and
`tryLock` returned `false` satisfies it, and that is exactly the case the standard leaves undefined —
the A2 control in `Test/Control.lean` says so in as many words. So the axiom carries the non-ownership
precondition the standard requires, and concludes both that the owner is unchanged **and** that it is
not the caller. Without the second conjunct nothing downstream could use a failed `tryLock` to
establish anything, which is the whole point of `false`. -/
axiom tryLock_spec {r : Rep} {m : Std.BaseMutex} {w w' : World} {l : LockId} {t : Tid} {b : Bool} :
    IsLock r m l → (w.locks l).owner ≠ some t →
    Runs t (Std.BaseMutex.tryLock m) w b w' →
    (b = true → (w'.locks l).owner = some t) ∧
    (b = false → (w'.locks l).owner = (w.locks l).owner ∧ (w'.locks l).owner ≠ some t) ∧
    w.SameClock w'

/-- **A3 — release.** `lean_io_basemutex_unlock` (`mutex.cpp:37`) → `std::mutex::unlock`.

Requires ownership — releasing without holding is undefined behaviour, which is why the model has no
transition for it (`unlock_without_ownership_has_no_transition`). -/
axiom unlock_spec {r : Rep} {m : Std.BaseMutex} {w w' : World} {l : LockId} {t : Tid} :
    IsLock r m l → (w.locks l).owner = some t →
    Runs t (Std.BaseMutex.unlock m) w () w' → (w'.locks l).owner = none ∧ w.SameClock w'

/-! ### A4–A5 — the condition variable -/

/-- **A4 — waiting.** `lean_io_condvar_wait` (`mutex.cpp:55`) → `std::condition_variable::wait`, under
`std::adopt_lock_t`; ISO C++ `[thread.condition.condvar]`.

The runtime call is the *whole* park-and-resume: it releases the mutex, blocks, and re-acquires before
returning. So on return the lock is held again.

**The call spans a path, and the axiom states its endpoints.** To its caller `wait` is one
operation; in the model it is three steps — park (`afterWait` releases the lock and enrols the waiter),
resume, re-acquire — which `World.wait_cycle_reachable` exhibits and `World.afterWait_releases` shows
cannot be collapsed into one, since the model's own `wait` step leaves the lock free.

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
    {l : LockId} {t : Tid} :
    IsCondvar r cv c → IsLock r m l → (w.locks l).owner = some t →
    Runs t (Std.Condvar.wait cv m) w () w' →
    (w'.locks l).owner = some t ∧ t ∉ (w'.condvars c).waiters ∧ w.SameClock w'

/-- **A5 — notification, and its absence of memory.** `lean_io_condvar_notify_one`
(`mutex.cpp:62`) → `std::condition_variable::notify_one`.

Never *adds* a waiter, and it unblocks **at most one**, so the waiter set can lose at most one entry.
That it can be **lost entirely** when nobody is waiting is not a concession — it is proved, as
`notifyOne_no_waiters` in `World.lean`.

**This is not the same proposition as `notifyAll_spec`.** "At most one leaves" is what distinguishes
the two, and without it the pair says nothing about either: a `notifyOne` that wakes nobody and a
`notifyAll` that wakes nobody both satisfy a bare "does not grow" clause. -/
axiom notifyOne_spec {r : Rep} {cv : Std.Condvar} {w w' : World} {c : CondvarId} {t : Tid} :
    IsCondvar r cv c → Runs t (Std.Condvar.notifyOne cv) w () w' →
    (w'.condvars c).waiters.length ≤ (w.condvars c).waiters.length ∧
    (w.condvars c).waiters.length ≤ (w'.condvars c).waiters.length + 1 ∧
    w.SameClock w'

/-- **A5 — broadcast.** `lean_io_condvar_notify_all` (`mutex.cpp:67`).

Every thread that was waiting is released — it moves to *blocked on the mutex* rather than on the
condition variable — so every waiter present at the call is gone from the set afterwards, and the set
does not grow. This is what the shutdown path relies on.

It is therefore **not** the same proposition as `notifyOne_spec`, and the difference is not cosmetic: a
bare "does not grow" clause admits a `notifyAll` that releases nobody, which would leave the shutdown
argument proved of the model and never carried across the bridge. -/
axiom notifyAll_spec {r : Rep} {cv : Std.Condvar} {w w' : World} {c : CondvarId} {t : Tid} :
    IsCondvar r cv c → Runs t (Std.Condvar.notifyAll cv) w () w' →
    (w'.condvars c).waiters.length ≤ (w.condvars c).waiters.length ∧
    (∀ u, u ∈ (w.condvars c).waiters → u ∉ (w'.condvars c).waiters) ∧
    w.SameClock w'

/-! ### A7 — the clock -/

/-- **A7 — monotone time.** `lean_io_mono_nanos_now` (`object.cpp:421`).

Three conjuncts, and the third is the one that was missing. Reading the clock does not move model time;
the reading is recorded as the last sample; and it is never behind that previous sample. The first keeps
reads side-effect-free. The second and third together are what make *successive* readings comparable,
and therefore what makes a budget meaningful — without the second, two readings were related only to a
clock that no read moved, and "the clock never goes backwards" stayed a property of the runtime that no
theorem could use. Equal readings are permitted: the native clock has finite resolution. -/
axiom clock_spec {w w' : World} {n : Nat} {t : Tid} :
    Runs t (IO.monoNanosNow : BaseIO Nat) w n w' →
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
theorem calls_compose {r : Rep} {cv : Std.Condvar} {m : Std.BaseMutex} {c : CondvarId} {l : LockId}
    {t : Tid} {w₁ w₂ w₃ w₄ : World}
    (hL : IsLock r m l) (hC : IsCondvar r cv c)
    (h₁ : Runs t (Std.BaseMutex.lock m) w₁ () w₂)
    (h₂ : Runs t (Std.Condvar.wait cv m) w₂ () w₃)
    (h₃ : Runs t (Std.BaseMutex.unlock m) w₃ () w₄) :
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
    (h₁ : Runs t (IO.monoNanosNow : BaseIO Nat) w₁ n₁ w₂)
    (h₂ : Runs t (Std.BaseMutex.lock m) w₂ () w₃)
    (h₃ : Runs t (IO.monoNanosNow : BaseIO Nat) w₃ n₂ w₄) :
    n₁ ≤ n₂ := by
  have hs : w₂.lastSample = some n₁ := (clock_spec h₁).2.1
  have hpres : w₃.lastSample = w₂.lastSample := by
    have := (lock_spec hL h₂).2
    simp [World.SameClock] at this
    exact this.2
  have hbound : ∀ s, w₃.lastSample = some s → s ≤ n₂ := (clock_spec h₃).2.2
  exact hbound n₁ (by rw [hpres, hs])


/-! ### The audit

`#print axioms` is the TCB check from `PLAN.md` §6: the theorems in `World.lean` should name nothing,
proving that the model's properties are not assumed. -/

#print axioms LeanIn.notifyOne_no_waiters
#print axioms LeanIn.reacquisition_while_others_wait
#print axioms LeanIn.wait_cycle_reachable
#print axioms LeanIn.afterWait_releases
#print axioms LeanIn.reacquisition_is_anyone

end LeanIn
