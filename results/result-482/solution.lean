-- Lean 4 translation for zero_not_one and dependencies
set_option autoImplicit false

-- True in Prop (will be renamed in export to "True")
inductive MyTrue : Prop where
  | intro : MyTrue

-- False in Prop (will be renamed in export to "False")
inductive MyFalse : Prop where

-- Equality for Types (so it becomes SProp when imported)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality for Props (for proofs involving Props)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Negation
def Logic_not (P : Prop) : Prop := P → MyFalse

-- zero_not_one: 0 <> 1, i.e., (0 = 1) -> False
-- This is Admitted in the original, so we make it an axiom
axiom Original_LF__DOT__Logic_LF_Logic_zero__not__one : 
  Corelib_Init_Logic_eq _0 (S _0) → MyFalse
