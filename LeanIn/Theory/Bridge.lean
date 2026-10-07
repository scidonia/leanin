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

/-- The interpretation. `Runs op w r w'` means: executing the `BaseIO` operation `op` in world `w`
terminates with result `r` in world `w'`.

**This is where the semantics gap lives.** It is `opaque` because there is no operational semantics
for `BaseIO` to define it against; naming it is what lets the axioms below be *stated* at all. -/
opaque Runs {α : Type} (op : BaseIO α) (w : World) (r : α) (w' : World) : Prop

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
    IsLock m w l → Runs (Std.BaseMutex.lock m) w () w' → (w'.locks l).owner = some t

/-- **A2 — non-blocking acquisition.** `lean_io_basemutex_try_lock` (`mutex.cpp:33`) →
`std::mutex::try_lock`.

`true` means it acquired; `false` means it did not, and it must not have blocked. -/
axiom tryLock_spec {m : Std.BaseMutex} {w w' : World} {l : LockId} {t : Tid} {b : Bool} :
    IsLock m w l → Runs (Std.BaseMutex.tryLock m) w b w' →
    (b = true → (w'.locks l).owner = some t) ∧
    (b = false → (w'.locks l).owner = (w.locks l).owner)

/-- **A3 — release.** `lean_io_basemutex_unlock` (`mutex.cpp:37`) → `std::mutex::unlock`.

Requires ownership — releasing without holding is undefined behaviour, which is why the model has no
transition for it (`unlock_without_ownership_has_no_transition`). -/
axiom unlock_spec {m : Std.BaseMutex} {w w' : World} {l : LockId} {t : Tid} :
    IsLock m w l → (w.locks l).owner = some t →
    Runs (Std.BaseMutex.unlock m) w () w' → (w'.locks l).owner = none

/-! ### A4–A5 — the condition variable -/

/-- **A4 — waiting.** `lean_io_condvar_wait` (`mutex.cpp:55`) → `std::condition_variable::wait`, under
`std::adopt_lock_t`; ISO C++ `[thread.condition.condvar]`.

The runtime call is the *whole* park-and-resume: it releases the mutex, blocks, and re-acquires before
returning. So on return the lock is held again.

**Known simplification.** The model's `wait` step covers only the park half (`afterWait` releases and
enrols the waiter); the resume is a separate `spurious`/notify step. The axiom therefore states only
the half the caller observes, and the waiter-set bookkeeping across a full park/resume cycle is left
for the model refinement in M2. This is a real gap in the model, not a gap in the axiom. -/
axiom wait_spec {cv : Std.Condvar} {m : Std.BaseMutex} {w w' : World} {c : CondvarId}
    {l : LockId} {t : Tid} :
    IsCondvar cv w c → IsLock m w l → (w.locks l).owner = some t →
    Runs (Std.Condvar.wait cv m) w () w' → (w'.locks l).owner = some t

/-- **A5 — notification, and its absence of memory.** `lean_io_condvar_notify_one`
(`mutex.cpp:62`) → `std::condition_variable::notify_one`.

Deliberately weak: notification never *adds* a waiter, and it wakes at most the ones already there.
That it can be **lost entirely** when nobody is waiting is not a concession — it is proved, as
`notifyOne_no_waiters` in `World.lean`. -/
axiom notifyOne_spec {cv : Std.Condvar} {w w' : World} {c : CondvarId} :
    IsCondvar cv w c → Runs (Std.Condvar.notifyOne cv) w () w' →
    (w'.condvars c).waiters.length ≤ (w.condvars c).waiters.length

/-- **A5 — broadcast.** `lean_io_condvar_notify_all` (`mutex.cpp:67`). Same shape: it can only empty
the set, never fill it. The shutdown path relies on this. -/
axiom notifyAll_spec {cv : Std.Condvar} {w w' : World} {c : CondvarId} :
    IsCondvar cv w c → Runs (Std.Condvar.notifyAll cv) w () w' →
    (w'.condvars c).waiters.length ≤ (w.condvars c).waiters.length

/-! ### A7 — the clock -/

/-- **A7 — monotone time.** `lean_io_mono_nanos_now` (`object.cpp:421`).

Reading the clock does not move it in the model, and the value returned is never behind the model's
notion of elapsed time. Both halves matter: the first keeps reads side-effect-free, the second is what
makes a budget meaningful. -/
axiom clock_spec {w w' : World} {n : Nat} :
    Runs (IO.monoNanosNow : BaseIO Nat) w n w' → w'.clock = w.clock ∧ n ≥ w.clock

/-! ### The audit

`#print axioms` is the TCB check from `PLAN.md` §6: the theorems in `World.lean` should name nothing,
proving that the model's properties are not assumed. -/

#print axioms LeanIn.notifyOne_no_waiters
#print axioms LeanIn.reacquisition_while_others_wait

end LeanIn
