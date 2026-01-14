-- Lean 4 translation for mul_0_r' and its dependencies

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

-- We need to export True - use a namespace to avoid the clash with Lean's True
namespace Exports
def «True» : Prop := PTrue
end Exports

-- Define equality in Prop (becomes SProp when imported)
inductive Corelib_Init_Logic_eq {A : Type} : A -> A -> Prop where
  | refl : (a : A) -> Corelib_Init_Logic_eq a a

-- Define equality on Prop (for Props which become SProp)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A -> A -> Prop where
  | refl : (a : A) -> Corelib_Init_Logic_eq_Prop a a

-- mul_0_r' : forall n:nat, n * 0 = 0
-- This is Admitted in Original.v, so we translate it as an axiom
axiom Original_LF__DOT__IndPrinciples_LF_IndPrinciples_mul__0__r' :
  forall (n : nat), Corelib_Init_Logic_eq (Nat_mul n _0) _0
