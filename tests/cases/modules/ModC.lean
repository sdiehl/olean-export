module

prelude
public import ModB
import all ModA

noncomputable section

theorem thmC : Eq hiddenBody (Nat.succ Nat.zero) := Eq.refl _

public theorem thmC' : Eq Nat.zero Nat.zero := thmB

end
