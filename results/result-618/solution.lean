-- True in Prop (will become SProp in Rocq)
inductive _True : Prop where
  | I : _True

def _True_I : _True := _True.I

-- Equality in Prop (will become SProp in Rocq)
inductive eq' {A : Type} : A → A → Prop where
  | refl (a : A) : eq' a a

def Corelib_Init_Logic_eq {A : Type} (x y : A) : Prop := eq' x y
def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a := eq'.refl a

-- Equality over Prop (will become SProp -> SProp -> SProp in Rocq)
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

-- repeat function
def Original_LF__DOT__Poly_LF_Poly_repeat (X : Type) (x : X) (count : nat) : Original_LF__DOT__Poly_LF_Poly_list X :=
  match count with
  | nat.O => Original_LF__DOT__Poly_LF_Poly_list.nil
  | nat.S count' => Original_LF__DOT__Poly_LF_Poly_list.cons x (Original_LF__DOT__Poly_LF_Poly_repeat X x count')

-- test_repeat1 : repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat))
-- This is admitted in Rocq, so we axiomatize it
axiom Original_LF__DOT__Poly_LF_Poly_test__repeat1 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Poly_LF_Poly_repeat nat (S (S (S (S _0)))) (S (S _0)))
    (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S (S _0))))
       (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S (S _0)))) (Original_LF__DOT__Poly_LF_Poly_nil nat)))
