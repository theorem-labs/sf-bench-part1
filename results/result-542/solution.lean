/-
  Lean translation for in_not_nil and all dependencies
  
  Required definitions:
  - Original.LF_DOT_Poly.LF.Poly.list
  - Original.LF_DOT_Poly.LF.Poly.nil
  - Original.LF_DOT_Poly.LF.Poly.cons
  - Original.LF_DOT_Logic.LF.Logic.In
  - Original.False
  - False
  - True
  - Logic.not
  - Corelib.Init.Logic.eq
  - Original.LF_DOT_Logic.LF.Logic.in_not_nil (Admitted axiom)
-/

set_option autoImplicit false

-- False in Prop (will become SProp in Rocq)
-- Named "MyFalse" to avoid conflict, will be renamed in .out
inductive MyFalse : Prop where

-- Original.False is an alias to MyFalse
abbrev Original_False := MyFalse

-- True in Prop (will become SProp in Rocq)
-- Named "TrueProp" to avoid conflict with built-in True  
inductive TrueProp : Prop where
  | I : TrueProp

-- Equality in Prop (will become SProp in Rocq)
-- Using eq' to get Imported.eq' naming
universe u
inductive eq' {A : Sort u} : A → A → Prop where
  | refl (a : A) : eq' a a

def Corelib_Init_Logic_eq {A : Type} (x y : A) : Prop := eq' x y
def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a := eq'.refl a

-- Prop-level equality (for SProp in Rocq)
def Corelib_Init_Logic_eq_Prop {A : Prop} (x y : A) : Prop := eq' x y

-- Polymorphic list type matching Original.LF_DOT_Poly.LF.Poly.list
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

-- List constructors as explicit definitions
def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

def Original_LF__DOT__Poly_LF_Poly_cons (X : Type) : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons

-- Logic.not (negation) - defined in terms of our False
def Logic_not (P : Prop) : Prop := P → MyFalse

-- In predicate: checks if x is in the list
def Original_LF__DOT__Logic_LF_Logic_In {A : Type} (x : A) (l : Original_LF__DOT__Poly_LF_Poly_list A) : Prop :=
  match l with
  | Original_LF__DOT__Poly_LF_Poly_list.nil => Original_False
  | Original_LF__DOT__Poly_LF_Poly_list.cons x' l' => eq' x' x ∨ Original_LF__DOT__Logic_LF_Logic_In x l'

-- in_not_nil is an admitted axiom in Original.v
-- Theorem in_not_nil : forall A (x : A) (l : list A), In x l -> l <> [].
-- Expands to: forall A (x : A) (l : list A), In x l -> (l = []) -> False
axiom Original_LF__DOT__Logic_LF_Logic_in__not__nil :
  ∀ (A : Type) (x : A) (l : Original_LF__DOT__Poly_LF_Poly_list A),
    Original_LF__DOT__Logic_LF_Logic_In x l →
    Corelib_Init_Logic_eq l (Original_LF__DOT__Poly_LF_Poly_nil A) → MyFalse
