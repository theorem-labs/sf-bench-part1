-- Equality in Type (not Prop)
inductive eq {A : Type} : A → A → Type where
  | refl (a : A) : eq a a

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

-- List append function
def Original_LF__DOT__Poly_LF_Poly_app {X : Type} : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X
  | Original_LF__DOT__Poly_LF_Poly_list.nil, l2 => l2
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t, l2 => Original_LF__DOT__Poly_LF_Poly_list.cons h (Original_LF__DOT__Poly_LF_Poly_app t l2)

-- List reverse function
def Original_LF__DOT__Poly_LF_Poly_rev {X : Type} : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X
  | Original_LF__DOT__Poly_LF_Poly_list.nil => Original_LF__DOT__Poly_LF_Poly_list.nil
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t => Original_LF__DOT__Poly_LF_Poly_app (Original_LF__DOT__Poly_LF_Poly_rev t) (Original_LF__DOT__Poly_LF_Poly_list.cons h Original_LF__DOT__Poly_LF_Poly_list.nil)

-- Equality constructor
def Corelib_Init_Logic_eq {A : Type} (x y : A) : Type := eq x y

-- The test_rev1 axiom
axiom Original_LF__DOT__Poly_LF_Poly_test__rev1 : 
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Poly_LF_Poly_rev
       (Original_LF__DOT__Poly_LF_Poly_cons (S _0)
          (Original_LF__DOT__Poly_LF_Poly_cons (S (S _0)) (Original_LF__DOT__Poly_LF_Poly_nil nat))))
    (Original_LF__DOT__Poly_LF_Poly_cons (S (S _0))
       (Original_LF__DOT__Poly_LF_Poly_cons (S _0) (Original_LF__DOT__Poly_LF_Poly_nil nat)))