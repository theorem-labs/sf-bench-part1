-- Lean 4 translation for disc_example and dependencies
set_option autoImplicit false

-- True in Prop (becomes SProp when imported to Rocq)
inductive PTrue : Prop where
  | intro : PTrue

-- False in Prop (becomes SProp when imported to Rocq)
inductive PFalse : Prop where

-- Equality in Prop for Type arguments (becomes SProp when imported to Rocq)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality in Prop for Prop arguments (becomes SProp when imported to Rocq)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Negation
def Logic_not (P : Prop) : Prop := P → PFalse

-- disc_example: forall n, ~ (O = S n)
-- This is Admitted in the original, so we make it an axiom
axiom Original_LF__DOT__Logic_LF_Logic_disc__example : 
  ∀ (n : nat), Corelib_Init_Logic_eq _0 (S n) → PFalse
