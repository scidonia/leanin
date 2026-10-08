import Std
import LeanIn.Theory.World

/-!
# The bridge: the only axioms

`World.lean` proves the *model's* properties — mutual exclusion, no notification memory, permitted
spurious wakeups, no fairness. None of that is assumed. What is assumed is the connection between
that model and the running program, and this file is the whole of it.

Everything here is an `axiom`, so `#print axioms` on any theorem downstream will name exactly what it
rests on. There are seven, and they are the TCB (D7).

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
case had no way to conclude that *the caller* had failed. -/
opaque Runs {α : Type} (t : Tid) (op : BaseIO α) (w : World) (r : α) (w' : World) : Prop

/-- Representation: the runtime lock `m` is the model lock at index `l`. Opaque, because the runtime
object is a C++ `std::mutex` behind an `external` — there is no Lean structure to inspect. -/
opaque IsLock (m : Std.BaseMutex) (w : World) (l : LockId) : Prop

/-- Representation: the runtime condition variable `cv` is the model condvar at `c`. -/
opaque IsCondvar (cv : Std.Condvar) (w : World) (c : CondvarId) : Prop

/-! ### A1–A2 — the mutex -/

/-- **A1 — acquisition.** `lean_io_basemutex_lock` (`mutex.cpp:27`) → `std::mutex::lock`; ISO C++
`[thread.mutex.requirements.mutex]`.

A successful acquisition is observed as ownership of the corresponding model lock. The *blocking*
case is not modelled as a transition: an operation that has not returned has not stepped.

Stated as a property of the returned world rather than an equality with `afterLock w l t`, so that the
world is not forced to be *only* what the model says — the mutex is free to have other effects the
model does not track. -/
axiom lock_spec {m : Std.BaseMutex} {w w' : World} {l : LockId} {t : Tid} :
    IsLock m w l → Runs t (Std.BaseMutex.lock m) w () w' → (w'.locks l).owner = some t

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
axiom tryLock_spec {m : Std.BaseMutex} {w w' : World} {l : LockId} {t : Tid} {b : Bool} :
    IsLock m w l → (w.locks l).owner ≠ some t →
    Runs t (Std.BaseMutex.tryLock m) w b w' →
    (b = true → (w'.locks l).owner = some t) ∧
    (b = false → (w'.locks l).owner = (w.locks l).owner ∧ (w'.locks l).owner ≠ some t)

/-- **A3 — release.** `lean_io_basemutex_unlock` (`mutex.cpp:37`) → `std::mutex::unlock`.

Requires ownership — releasing without holding is undefined behaviour, which is why the model has no
transition for it (`unlock_without_ownership_has_no_transition`). -/
axiom unlock_spec {m : Std.BaseMutex} {w w' : World} {l : LockId} {t : Tid} :
    IsLock m w l → (w.locks l).owner = some t →
    Runs t (Std.BaseMutex.unlock m) w () w' → (w'.locks l).owner = none

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
axiom wait_spec {cv : Std.Condvar} {m : Std.BaseMutex} {w w' : World} {c : CondvarId}
    {l : LockId} {t : Tid} :
    IsCondvar cv w c → IsLock m w l → (w.locks l).owner = some t →
    Runs t (Std.Condvar.wait cv m) w () w' →
    (w'.locks l).owner = some t ∧ t ∉ (w'.condvars c).waiters

/-- **A5 — notification, and its absence of memory.** `lean_io_condvar_notify_one`
(`mutex.cpp:62`) → `std::condition_variable::notify_one`.

Deliberately weak: notification never *adds* a waiter, and it wakes at most the ones already there.
That it can be **lost entirely** when nobody is waiting is not a concession — it is proved, as
`notifyOne_no_waiters` in `World.lean`. -/
axiom notifyOne_spec {cv : Std.Condvar} {w w' : World} {c : CondvarId} {t : Tid} :
    IsCondvar cv w c → Runs t (Std.Condvar.notifyOne cv) w () w' →
    (w'.condvars c).waiters.length ≤ (w.condvars c).waiters.length

/-- **A5 — broadcast.** `lean_io_condvar_notify_all` (`mutex.cpp:67`). Same shape: it can only empty
the set, never fill it. The shutdown path relies on this. -/
axiom notifyAll_spec {cv : Std.Condvar} {w w' : World} {c : CondvarId} {t : Tid} :
    IsCondvar cv w c → Runs t (Std.Condvar.notifyAll cv) w () w' →
    (w'.condvars c).waiters.length ≤ (w.condvars c).waiters.length

/-! ### A7 — the clock -/

/-- **A7 — monotone time.** `lean_io_mono_nanos_now` (`object.cpp:421`).

Reading the clock does not move it in the model, and the value returned is never behind the model's
notion of elapsed time. Both halves matter: the first keeps reads side-effect-free, the second is what
makes a budget meaningful. -/
axiom clock_spec {w w' : World} {n : Nat} {t : Tid} :
    Runs t (IO.monoNanosNow : BaseIO Nat) w n w' → w'.clock = w.clock ∧ n ≥ w.clock

/-! ### The audit

`#print axioms` is the TCB check from `PLAN.md` §6: the theorems in `World.lean` should name nothing,
proving that the model's properties are not assumed. -/

#print axioms LeanIn.notifyOne_no_waiters
#print axioms LeanIn.reacquisition_while_others_wait
#print axioms LeanIn.wait_cycle_reachable
#print axioms LeanIn.afterWait_releases
#print axioms LeanIn.reacquisition_is_anyone

end LeanIn
