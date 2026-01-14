-- Lean translation for LF.Poly definitions

-- True in Prop (will become SProp in Rocq)  
-- We define MyTrue since True already exists in Lean stdlib
inductive MyTrue : Prop where
  | I : MyTrue

-- Equality in Prop (will become SProp in Rocq)
inductive eq' {A : Type} : A → A → Prop where
  | refl (a : A) : eq' a a

def Corelib_Init_Logic_eq {A : Type} (x y : A) : Prop := eq' x y
def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a := eq'.refl a

-- Equality for Prop types (also Prop, will become SProp in Rocq)
inductive eq'_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : eq'_Prop a a

def Corelib_Init_Logic_eq_Prop {A : Prop} (x y : A) : Prop := eq'_Prop x y
def Corelib_Init_Logic_eq_Prop_refl {A : Prop} (a : A) : Corelib_Init_Logic_eq_Prop a a := eq'_Prop.refl a

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

-- app function
def Original_LF__DOT__Poly_LF_Poly_app {X : Type} (l1 l2 : Original_LF__DOT__Poly_LF_Poly_list X) : Original_LF__DOT__Poly_LF_Poly_list X :=
  match l1 with
  | Original_LF__DOT__Poly_LF_Poly_list.nil => l2
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t => Original_LF__DOT__Poly_LF_Poly_list.cons h (Original_LF__DOT__Poly_LF_Poly_app t l2)

-- rev function
def Original_LF__DOT__Poly_LF_Poly_rev {X : Type} (l : Original_LF__DOT__Poly_LF_Poly_list X) : Original_LF__DOT__Poly_LF_Poly_list X :=
  match l with
  | Original_LF__DOT__Poly_LF_Poly_list.nil => Original_LF__DOT__Poly_LF_Poly_list.nil
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t => 
      Original_LF__DOT__Poly_LF_Poly_app (Original_LF__DOT__Poly_LF_Poly_rev t) 
        (Original_LF__DOT__Poly_LF_Poly_list.cons h Original_LF__DOT__Poly_LF_Poly_list.nil)

-- test_rev1: rev [1;2] = [2;1]
-- rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil))
-- This is an Admitted theorem in Original.v, so we axiomatize it
axiom Original_LF__DOT__Poly_LF_Poly_test__rev1 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Poly_LF_Poly_rev
       (Original_LF__DOT__Poly_LF_Poly_cons (S _0)
          (Original_LF__DOT__Poly_LF_Poly_cons (S (S _0)) (Original_LF__DOT__Poly_LF_Poly_nil nat))))
    (Original_LF__DOT__Poly_LF_Poly_cons (S (S _0))
       (Original_LF__DOT__Poly_LF_Poly_cons (S _0) (Original_LF__DOT__Poly_LF_Poly_nil nat)))
