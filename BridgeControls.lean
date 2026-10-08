import Std

import LeanIn.Test.BridgeControls

/-- Entry point for the representation-dependence controls. Body lives in `LeanIn.Test.BridgeControls`.

With no argument it runs every control and every trace. With one, it runs only that trace, which is how a
hang gets isolated to the trace that caused it. -/
def main (args : List String) : IO UInt32 :=
  match args with
  | name :: _ => LeanIn.bridgeControlsOne name
  | [] => LeanIn.bridgeControlsMain
