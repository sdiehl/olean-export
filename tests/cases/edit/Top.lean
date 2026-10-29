prelude
import Base

noncomputable section

mutual
  inductive Even : N → Prop
    | zero : Even N.zero
    | succ {n : N} : Odd n → Even (N.succ n)
  inductive Odd : N → Prop
    | succ {n : N} : Even n → Odd (N.succ n)
end

abbrev two : N := N.succ (N.succ N.zero)

def three : N := N.succ two

end
