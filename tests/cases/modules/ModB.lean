module

prelude
public import Extra
import ModA

public section

noncomputable section

theorem thmB : Eq Nat.zero Nat.zero := thmA

def viaHidden : Nat := hiddenBody

end
end
