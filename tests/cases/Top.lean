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

abbrev two : N := N.add (N.succ N.zero) (N.succ N.zero)

def letty (n : N) : N :=
  let m := N.add n n
  N.add m m

end
