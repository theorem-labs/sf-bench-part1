-- Lean 4 translation for mult_n_0_m_0 and its dependencies

-- Define nat as an inductive type to match Rocq's nat
inductive nat : Type where
  | O : nat
  | S : nat -> nat

-- Define Nat_add to match Rocq's Nat.add
def Nat_add : nat -> nat -> nat
  | nat.O, m => m
  | nat.S p, m => nat.S (Nat_add p m)

-- Define Nat_mul to match Rocq's Nat.mul
def Nat_mul : nat -> nat -> nat
  | nat.O, _ => nat.O
  | nat.S p, m => Nat_add m (Nat_mul p m)

-- Aliases for 0 and S
def _0 : nat := nat.O
def S : nat -> nat := nat.S

-- True in Prop
inductive PTrue : Prop where
  | intro : PTrue

namespace Defs
  def True : Prop := PTrue
end Defs

-- Define equality in Prop (becomes SProp when imported)
inductive Corelib_Init_Logic_eq {A : Type} : A -> A -> Prop where
  | refl : (a : A) -> Corelib_Init_Logic_eq a a

-- Define equality for Prop (becomes SProp -> SProp when imported)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A -> A -> Prop where
  | refl : (a : A) -> Corelib_Init_Logic_eq_Prop a a

-- The main theorem - mult_n_0_m_0 is Admitted in Original.v
-- forall p q : nat, (p * 0) + (q * 0) = 0
axiom Original_LF__DOT__Basics_LF_Basics_mult__n__0__m__0 :
  ∀ (p q : nat), Corelib_Init_Logic_eq (Nat_add (Nat_mul p _0) (Nat_mul q _0)) _0
