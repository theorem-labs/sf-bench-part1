-- True in Prop (will become SProp in Rocq)
inductive TrueProp : Prop where
  | I : TrueProp

-- Equality in Prop (will become SProp in Rocq)
inductive eq' {A : Type} : A → A → Prop where
  | refl (a : A) : eq' a a

def Corelib_Init_Logic_eq {A : Type} (x y : A) : Prop := eq' x y
def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a := eq'.refl a

-- Equality for Prop types (will be imported as SProp -> SProp -> SProp -> SProp)
inductive eq'_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : eq'_Prop a a

def Corelib_Init_Logic_eq_Prop {A : Prop} (x y : A) : Prop := eq'_Prop x y

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Polymorphic list type
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

-- List constructors
def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

def Original_LF__DOT__Poly_LF_Poly_cons {X : Type} : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons

-- Length function
def Original_LF__DOT__Poly_LF_Poly_length {X : Type} : Original_LF__DOT__Poly_LF_Poly_list X → nat
  | Original_LF__DOT__Poly_LF_Poly_list.nil => nat.O
  | Original_LF__DOT__Poly_LF_Poly_list.cons _ t => nat.S (Original_LF__DOT__Poly_LF_Poly_length t)

-- test_length1: length [1; 2; 3] = 3
-- This is admitted in Original.v, so we provide it as an axiom
axiom Original_LF__DOT__Poly_LF_Poly_test__length1 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Poly_LF_Poly_length
       (Original_LF__DOT__Poly_LF_Poly_cons (S _0)
          (Original_LF__DOT__Poly_LF_Poly_cons (S (S _0))
             (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S _0))) (Original_LF__DOT__Poly_LF_Poly_nil nat)))))
    (S (S (S _0)))
