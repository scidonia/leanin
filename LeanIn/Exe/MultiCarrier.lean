module

import LeanIn

/-- `lake exe multiCarrier` runs 64 shared-spawned tasks that sleep, on three carriers, and checks that more
than one carrier thread ran them. -/
public def main : IO UInt32 := do
  let e ← LeanIn.Sched.Executor.new LeanIn.Task.Item 256 3
  let tids ← IO.mkRef ([] : List UInt64)
  let child : LeanIn.Task.EAsync IO.Error Unit :=
    ⟨fun k ctx => do
      let tid ← IO.getTID
      tids.modify (fun xs => tid :: xs)
      IO.sleep 20
      k (.ok ()) ctx⟩
  let root : LeanIn.Task.EAsync IO.Error Unit := do
    let mut hs : List (LeanIn.Task.Task (Except IO.Error Unit)) := []
    for _ in [0:64] do
      hs := (← monadLift (LeanIn.Runtime.spawnShared e child)) :: hs
    for h in hs do
      let _ ← LeanIn.Task.Async.await h
  let (_, _) ← LeanIn.Runtime.runCarriersWait e 3 root
  let seen ← tids.get
  let uniq := seen.eraseDups.length
  IO.println s!"multiCarrier|tasks={seen.length}|carriers={uniq}"
  return if seen.length == 64 && uniq >= 2 then 0 else 1
