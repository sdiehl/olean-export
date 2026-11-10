module

prelude
public import Extra

public section

set_option autoImplicit false

noncomputable section

def hiddenBody : Nat := Nat.succ Nat.zero

@[expose] def shownBody : Nat := Nat.zero

theorem thmA : Eq shownBody Nat.zero := Eq.refl _

private def secretA : Nat := Nat.zero

theorem usesSecret : Eq Nat.zero Nat.zero := Eq.refl secretA

end
end
