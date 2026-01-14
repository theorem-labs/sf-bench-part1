-- Equality in Prop (will be exported to SProp)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality in Prop for Prop types (will be exported to SProp)
-- This is needed for the Checker's expected interface
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- True type in Prop (will be imported as SProp in Rocq)
-- We use True_ as an alias since True is a Lean builtin
inductive True_ : Prop where
  | intro : True_

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

-- negb function
def Original_LF__DOT__Basics_LF_Basics_negb (b : Original_LF__DOT__Basics_LF_Basics_bool) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match b with
  | .Original_LF__DOT__Basics_LF_Basics_bool_true => .Original_LF__DOT__Basics_LF_Basics_bool_false
  | .Original_LF__DOT__Basics_LF_Basics_bool_false => .Original_LF__DOT__Basics_LF_Basics_bool_true

-- even function
def Original_LF__DOT__Basics_LF_Basics_even : nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O => .Original_LF__DOT__Basics_LF_Basics_bool_true
  | nat.S nat.O => .Original_LF__DOT__Basics_LF_Basics_bool_false
  | nat.S (nat.S n') => Original_LF__DOT__Basics_LF_Basics_even n'

-- odd function
def Original_LF__DOT__Basics_LF_Basics_odd (n : nat) : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_negb (Original_LF__DOT__Basics_LF_Basics_even n)

-- Polymorphic list type
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

-- List constructors
def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

def Original_LF__DOT__Poly_LF_Poly_cons {X : Type} : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons

-- filter function
def Original_LF__DOT__Poly_LF_Poly_filter {X : Type} (test : X → Original_LF__DOT__Basics_LF_Basics_bool) : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X
  | Original_LF__DOT__Poly_LF_Poly_list.nil => Original_LF__DOT__Poly_LF_Poly_list.nil
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t =>
    match test h with
    | Original_LF__DOT__Basics_LF_Basics_bool.Original_LF__DOT__Basics_LF_Basics_bool_true => Original_LF__DOT__Poly_LF_Poly_list.cons h (Original_LF__DOT__Poly_LF_Poly_filter test t)
    | Original_LF__DOT__Basics_LF_Basics_bool.Original_LF__DOT__Basics_LF_Basics_bool_false => Original_LF__DOT__Poly_LF_Poly_filter test t

-- test_filter1: filter even [1;2;3;4] = [2;4]
-- This is admitted in Original.v
axiom Original_LF__DOT__Poly_LF_Poly_test__filter1 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Poly_LF_Poly_filter Original_LF__DOT__Basics_LF_Basics_even
       (Original_LF__DOT__Poly_LF_Poly_cons (S _0)
          (Original_LF__DOT__Poly_LF_Poly_cons (S (S _0))
             (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S _0)))
                (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S (S _0)))) (Original_LF__DOT__Poly_LF_Poly_nil nat))))))
    (Original_LF__DOT__Poly_LF_Poly_cons (S (S _0))
       (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S (S _0)))) (Original_LF__DOT__Poly_LF_Poly_nil nat)))
