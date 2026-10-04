prelude

set_option autoImplicit false

universe u v

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type

noncomputable section

inductive Eq {α : Sort u} : α → α → Prop
  | refl (a : α) : Eq a a

init_quot

set_option bootstrap.inductiveCheckResultingUniverse false in
inductive PUnit : Sort u
  | unit

inductive N
  | zero
  | succ (n : N)

def N.add (m n : N) : N :=
  N.rec (motive := fun _ => N) m (fun _ ih => N.succ ih) n

theorem N.add_zero (m : N) : Eq (N.add m N.zero) m :=
  Eq.refl m

structure Pair (α : Type u) (β : Type v) where
  fst : α
  snd : β

def Pair.swap {α : Type u} {β : Type v} (p : Pair α β) : Pair β α :=
  ⟨p.2, p.1⟩

axiom choice {α : Sort u} : α

end
