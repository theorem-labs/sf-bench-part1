-- Lean 4 translation for eq_example3 and dependencies
set_option autoImplicit false

-- False in Prop (will become SProp in Rocq)
-- Using RocqFalse to avoid conflict with Lean's False
inductive RocqFalse : Prop where

-- True in Prop (will become SProp in Rocq)
inductive TrueProp : Prop where
  | I : TrueProp

-- Equality in Prop (will become SProp in Rocq)
inductive eq' {A : Type} : A → A → Prop where
  | refl (a : A) : eq' a a

def Corelib_Init_Logic_eq {A : Type} (x y : A) : Prop := eq' x y
def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a := eq'.refl a

-- Equality for Prop (will become SProp -> SProp -> SProp in Rocq)
inductive eq'_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : eq'_Prop a a

def Corelib_Init_Logic_eq_Prop {A : Prop} (x y : A) : Prop := eq'_Prop x y

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

-- eq_example3: [] <> h :: t  (Admitted in Rocq, so axiomatized here)
-- Expands to: forall (X : Type) (h : X) (t : list X), not ([] = h :: t)
-- i.e., (Corelib_Init_Logic_eq nil (cons h t)) -> False
axiom Original_LF__DOT__AltAuto_LF_AltAuto_eq__example3 :
  ∀ (X : Type) (h : X) (t : Original_LF__DOT__Poly_LF_Poly_list X),
    Corelib_Init_Logic_eq (Original_LF__DOT__Poly_LF_Poly_nil X) (Original_LF__DOT__Poly_LF_Poly_cons h t) → RocqFalse
