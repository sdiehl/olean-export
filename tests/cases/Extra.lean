module

prelude

public section

set_option autoImplicit false
set_option genCtorIdx false
set_option backward.linearNoConfusionType false

universe u v

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type

noncomputable section

inductive Eq {α : Sort u} : α → α → Prop
  | refl (a : α) : Eq a a

set_option bootstrap.inductiveCheckResultingUniverse false in
inductive PUnit : Sort u
  | unit

inductive Nat
  | zero
  | succ (n : Nat)

class OfNat (α : Type u) (_ : Nat) where
  ofNat : α

instance instOfNatNat (n : Nat) : OfNat Nat n := ⟨n⟩

def Nat.add (m n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) m (fun _ ih => Nat.succ ih) n

structure String where
  data : Nat

inductive List (α : Type u)
  | nil
  | cons (head : α) (tail : List α)

inductive Tree
  | node (children : List Tree)

def small : Nat := 42

def big : Nat := 123456789012345678901234567890

def greeting : String := "héllo\n\"world\""

def twice (n : Nat) : Nat :=
  have m := Nat.add n n
  Nat.add m m

private def hidden : Nat := Nat.zero

end
end
