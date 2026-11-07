prelude
import Base

noncomputable section

structure Pinned where
  n : N
  h : Eq (N.add n N.zero) n

def pinned : Pinned := ⟨N.zero, N.add_zero N.zero⟩

def shadow (N : Type) (x : N) : N := x

end
