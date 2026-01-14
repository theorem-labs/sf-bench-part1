-- Lean 4 translation for nil_is_not_cons and dependencies
set_option autoImplicit false

-- False in Prop (will become SProp in Rocq)
-- Named RocqFalse to avoid conflict with Lean's False
inductive RocqFalse : Prop where

-- True in Prop (will become SProp in Rocq)
inductive TrueProp : Prop where
  | I : TrueProp

def RocqTrue : Prop := TrueProp

-- Equality in Prop (will become SProp in Rocq)
inductive eq' {A : Type} : A → A → Prop where
  | refl (a : A) : eq' a a

def Corelib_Init_Logic_eq {A : Type} (x y : A) : Prop := eq' x y
def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a := eq'.refl a

-- Polymorphic list type
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

-- List constructors
def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

def Original_LF__DOT__Poly_LF_Poly_cons {X : Type} : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons

-- Logic.not (negation) - defined in terms of our False
def Logic_not (P : Prop) : Prop := P → RocqFalse

-- nil_is_not_cons: forall X (x : X) (xs : list X), ~ (nil = x :: xs)
-- This is Admitted in Original.v, so we axiomatize it here
axiom Original_LF__DOT__Logic_LF_Logic_nil__is__not__cons :
  ∀ (X : Type) (x : X) (xs : Original_LF__DOT__Poly_LF_Poly_list X),
    Corelib_Init_Logic_eq (Original_LF__DOT__Poly_LF_Poly_nil X) (Original_LF__DOT__Poly_LF_Poly_cons x xs) → RocqFalse
