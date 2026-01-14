-- Lean 4 translation for lia_succeed2 and its dependencies

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

-- True in Prop - use namespace to avoid conflict with stdlib True
namespace Rocq
inductive True : Prop where
  | intro : True
end Rocq

-- Define equality in Prop (becomes SProp when imported) - for Type arguments
inductive Corelib_Init_Logic_eq {A : Type} : A -> A -> Prop where
  | refl : (a : A) -> Corelib_Init_Logic_eq a a

-- Define equality in Prop for Prop arguments - becomes SProp over SProp when imported
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A -> A -> Prop where
  | refl : (a : A) -> Corelib_Init_Logic_eq_Prop a a

-- The main theorem - lia_succeed2 is Admitted in Original.v
-- forall n m : nat, n * m = m * n
axiom Original_LF__DOT__AltAuto_LF_AltAuto_lia__succeed2 :
  forall (n m : nat), Corelib_Init_Logic_eq (Nat_mul n m) (Nat_mul m n)
