module

public import Std

public import LeanIn.Test.Dynamics

public section

/-- Entry point for the model dynamics probe. Body lives in `LeanIn.Test.Dynamics`. -/
def main : IO UInt32 := LeanIn.Test.main

end
