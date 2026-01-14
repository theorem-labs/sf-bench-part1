-- Lean 4 translation for trans_eq_exercise and dependencies

set_option autoImplicit false

-- Define nat as an inductive type to match Rocq's nat
inductive nat : Type where
  | O : nat
  | S : nat -> nat

-- Define Nat_add to match Rocq's Nat.add
def Nat_add : nat -> nat -> nat
  | nat.O, m => m
  | nat.S p, m => nat.S (Nat_add p m)

-- True - alias to Lean's built-in True
-- We need to export it with a specific name
def True' : Prop := _root_.True
def True'_intro : True' := _root_.True.intro

-- Equality (in Type to match Rocq's eq)
inductive Corelib_Init_Logic_eq {A : Type} (a : A) : A -> Prop where
  | refl : Corelib_Init_Logic_eq a a

-- Equality on Prop (for Rocq's eq at Prop sort)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} (a : A) : A -> Prop where
  | refl : Corelib_Init_Logic_eq_Prop a a

-- minustwo function
def Original_LF__DOT__Basics_LF_Basics_minustwo : nat -> nat
  | nat.O => nat.O
  | nat.S nat.O => nat.O
  | nat.S (nat.S n') => n'

-- trans_eq_exercise is Admitted in Original.v, so we declare it as an axiom
axiom Original_LF__DOT__Tactics_LF_Tactics_trans__eq__exercise : 
  forall (n m o p : nat),
    Corelib_Init_Logic_eq m (Original_LF__DOT__Basics_LF_Basics_minustwo o) ->
    Corelib_Init_Logic_eq (Nat_add n p) m ->
    Corelib_Init_Logic_eq (Nat_add n p) (Original_LF__DOT__Basics_LF_Basics_minustwo o)
