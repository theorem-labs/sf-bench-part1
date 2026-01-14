-- Lean 4 translation for not_S_pred_n and dependencies
set_option autoImplicit false

-- True in Prop (will become SProp PTrue when imported)
inductive PTrue : Prop where
  | intro : PTrue

-- False in Prop (will become SProp PFalse when imported)
inductive PFalse : Prop where

-- Equality in Prop for Type (so it becomes SProp when imported)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality in Prop for Prop (for the Prop version of the isomorphism)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

-- Successor function
def S : nat → nat := nat.S

-- Predecessor function
def Nat_pred : nat → nat
  | nat.O => nat.O
  | nat.S n' => n'

-- Negation (not)
def Logic_not (P : Prop) : Prop := P → PFalse

-- The main axiom: not (forall n, S (pred n) = n)
-- This is Admitted in the original Rocq, so we use an axiom
axiom Original_LF__DOT__Logic_LF_Logic_not__S__pred__n :
  (∀ x : nat, Corelib_Init_Logic_eq (S (Nat_pred x)) x) → PFalse
