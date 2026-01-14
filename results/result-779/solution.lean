/-
  Lean translation for filter_not_empty_In and all dependencies
  
  Required definitions from the Interface:
  - nat
  - Original.LF_DOT_Basics.LF.Basics.bool
  - Original.LF_DOT_Basics.LF.Basics.true
  - Original.LF_DOT_Basics.LF.Basics.false
  - Original.LF_DOT_Basics.LF.Basics.eqb
  - Original.LF_DOT_Poly.LF.Poly.list
  - Original.LF_DOT_Poly.LF.Poly.nil
  - Original.LF_DOT_Poly.LF.Poly.cons
  - Original.LF_DOT_Poly.LF.Poly.filter
  - Original.LF_DOT_Logic.LF.Logic.In
  - Corelib.Init.Logic.eq
  - True
  - False
  - Logic.not
  - Original.False
  - Original.LF_DOT_IndProp.LF.IndProp.filter_not_empty_In (Admitted)
-/

set_option autoImplicit false

-- Equality in Prop (will be exported to SProp) - for Type arguments
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality for Prop types (needed for Prop-level equality) - for Prop arguments
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- True type in Prop (named True_ to avoid conflict with Lean's True)
inductive True_ : Prop where
  | intro : True_

-- False type in Prop (using MyFalse since False is reserved in Lean)
inductive MyFalse : Prop where

-- Original_False - for Original.False
def Original_False : Prop := MyFalse

-- Logic.not = fun P => P -> MyFalse  
def Logic_not (P : Prop) : Prop := P → MyFalse

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

-- eqb function (equality test for nat)
def Original_LF__DOT__Basics_LF_Basics_eqb : nat → nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.Original_LF__DOT__Basics_LF_Basics_bool_true
  | nat.O, nat.S _ => Original_LF__DOT__Basics_LF_Basics_bool.Original_LF__DOT__Basics_LF_Basics_bool_false
  | nat.S _, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.Original_LF__DOT__Basics_LF_Basics_bool_false
  | nat.S n', nat.S m' => Original_LF__DOT__Basics_LF_Basics_eqb n' m'

-- Polymorphic list type
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

-- List constructors
def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

def Original_LF__DOT__Poly_LF_Poly_cons (X : Type) : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons

-- filter function
def Original_LF__DOT__Poly_LF_Poly_filter {X : Type} (test : X → Original_LF__DOT__Basics_LF_Basics_bool) : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X
  | Original_LF__DOT__Poly_LF_Poly_list.nil => Original_LF__DOT__Poly_LF_Poly_list.nil
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t =>
    match test h with
    | Original_LF__DOT__Basics_LF_Basics_bool.Original_LF__DOT__Basics_LF_Basics_bool_true => 
        Original_LF__DOT__Poly_LF_Poly_list.cons h (Original_LF__DOT__Poly_LF_Poly_filter test t)
    | Original_LF__DOT__Basics_LF_Basics_bool.Original_LF__DOT__Basics_LF_Basics_bool_false => 
        Original_LF__DOT__Poly_LF_Poly_filter test t

-- In predicate: checks if x is in the list
def Original_LF__DOT__Logic_LF_Logic_In {A : Type} (x : A) (l : Original_LF__DOT__Poly_LF_Poly_list A) : Prop :=
  match l with
  | Original_LF__DOT__Poly_LF_Poly_list.nil => MyFalse
  | Original_LF__DOT__Poly_LF_Poly_list.cons x' l' => x' = x ∨ Original_LF__DOT__Logic_LF_Logic_In x l'

-- filter_not_empty_In is an admitted axiom in Original.v
-- Theorem filter_not_empty_In : forall n l,
--   filter (fun x => n =? x) l <> [] -> In n l.
axiom Original_LF__DOT__IndProp_LF_IndProp_filter__not__empty__In :
  ∀ (n : nat) (l : Original_LF__DOT__Poly_LF_Poly_list nat),
    (Corelib_Init_Logic_eq 
       (Original_LF__DOT__Poly_LF_Poly_filter (fun x => Original_LF__DOT__Basics_LF_Basics_eqb n x) l)
       (Original_LF__DOT__Poly_LF_Poly_nil nat) → MyFalse) →
    Original_LF__DOT__Logic_LF_Logic_In n l

-- Nat addition
def nat_add : nat → nat → nat
  | nat.O, m => m
  | nat.S n', m => nat.S (nat_add n' m)

-- count function (from LF.IndProp)
-- Fixpoint count n l :=
--   match l with
--   | [] => 0
--   | m :: l' => (if n =? m then 1 else 0) + count n l'
--   end.
def Original_LF__DOT__IndProp_LF_IndProp_count : nat → Original_LF__DOT__Poly_LF_Poly_list nat → nat :=
  fun n l =>
    match l with
    | Original_LF__DOT__Poly_LF_Poly_list.nil => nat.O
    | Original_LF__DOT__Poly_LF_Poly_list.cons m l' =>
        nat_add
          (match Original_LF__DOT__Basics_LF_Basics_eqb n m with
           | Original_LF__DOT__Basics_LF_Basics_bool.Original_LF__DOT__Basics_LF_Basics_bool_true => nat.S nat.O
           | Original_LF__DOT__Basics_LF_Basics_bool.Original_LF__DOT__Basics_LF_Basics_bool_false => nat.O)
          (Original_LF__DOT__IndProp_LF_IndProp_count n l')

-- eqbP_practice is an admitted theorem in Original.v
-- Theorem eqbP_practice : forall n l, count n l = 0 -> ~(In n l).
axiom Original_LF__DOT__IndProp_LF_IndProp_eqbP__practice :
  ∀ (n : nat) (l : Original_LF__DOT__Poly_LF_Poly_list nat),
    Corelib_Init_Logic_eq (Original_LF__DOT__IndProp_LF_IndProp_count n l) nat.O →
    Original_LF__DOT__Logic_LF_Logic_In n l → MyFalse
