module

public import Std

public import LeanIn.Test.Control
public import LeanIn.Test.Send
public import LeanIn.Test.ExecutorNarrowing

public section

/-- Entry point for the bridge-axiom controls. Body lives in `LeanIn.Test.Control`. -/
def main (args : List String) : IO UInt32 := LeanIn.Test.main args

end
