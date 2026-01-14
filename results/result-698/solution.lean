-- Equality in Prop (will be exported to SProp)
-- Type version - for types in Type
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Prop version - we use a universe-polymorphic version that specializes to Sort 0
-- But we need it to show up as taking SProp in Rocq
-- Use Type* which can be specialized
universe u_prop
inductive Corelib_Init_Logic_eq_Prop (A : Sort u_prop) : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop A a a

-- True type in Prop (will be imported as SProp in Rocq)
-- We use Lean's builtin True
def True' : Prop := True
def True'_intro : True' := True.intro

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Bool type
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | Original_LF__DOT__Basics_LF_Basics_bool_true : Original_LF__DOT__Basics_LF_Basics_bool
  | Original_LF__DOT__Basics_LF_Basics_bool_false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.Original_LF__DOT__Basics_LF_Basics_bool_true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.Original_LF__DOT__Basics_LF_Basics_bool_false

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

-- test_repeat2: repeat bool false 1 = cons bool false (nil bool)
-- This is admitted in Original.v
axiom Original_LF__DOT__Poly_LF_Poly_test__repeat2 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Poly_LF_Poly_repeat Original_LF__DOT__Basics_LF_Basics_bool Original_LF__DOT__Basics_LF_Basics_false (S _0))
    (Original_LF__DOT__Poly_LF_Poly_cons Original_LF__DOT__Basics_LF_Basics_false (Original_LF__DOT__Poly_LF_Poly_nil Original_LF__DOT__Basics_LF_Basics_bool))
