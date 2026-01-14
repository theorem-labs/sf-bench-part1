-- Lean 4 translation for the plus_O_n' theorem and its dependencies

set_option autoImplicit false

-- Define nat as an inductive type to match Rocq's nat
inductive nat : Type where
  | O : nat
  | S : nat -> nat

-- Define Nat_add to match Rocq's Nat.add  
def Nat_add : nat -> nat -> nat
  | nat.O, m => m
  | nat.S p, m => nat.S (Nat_add p m)

-- Define 0 constant
def _0 : nat := nat.O

-- Define MyTrue as an inductive type (to avoid name conflict with builtin True)
-- The Rocq isomorphism file will map this to Rocq's True
inductive MyTrue : Prop where
  | intro : MyTrue

-- Define equality (eq) type
inductive Corelib_Init_Logic_eq {A : Type} (a : A) : A -> Prop where
  | refl : Corelib_Init_Logic_eq a a

-- The theorem plus_O_n': forall n : nat, 0 + n = n
-- This is Admitted in Original.v, so we use an axiom
axiom Original_LF__DOT__Basics_LF_Basics_plus__O__n' : forall (n : nat), Corelib_Init_Logic_eq (Nat_add _0 n) n
