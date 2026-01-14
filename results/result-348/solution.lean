-- Lean 4 translation for the isomorphism problem

set_option autoImplicit false

-- Define nat as an inductive type to match Rocq's nat
inductive nat : Type where
  | O : nat
  | S : nat -> nat

-- Define Nat_add to match Rocq's Nat.add
def Nat_add : nat -> nat -> nat
  | nat.O, m => m
  | nat.S p, m => nat.S (Nat_add p m)

-- Can't redefine True directly, use True_ and we'll handle in Rocq
inductive True_ : Prop where
  | intro : True_

-- Define eq to match Rocq's eq
inductive Corelib_Init_Logic_eq {A : Type} (x : A) : A -> Prop where
  | refl : Corelib_Init_Logic_eq x x

-- Define double to match Rocq's LF.Induction.double
def Original_LF__DOT__Induction_LF_Induction_double : nat -> nat
  | nat.O => nat.O
  | nat.S n' => nat.S (nat.S (Original_LF__DOT__Induction_LF_Induction_double n'))

-- Define double_plus as an axiom since it's Admitted in the original
axiom Original_LF__DOT__Induction_LF_Induction_double__plus : 
  ∀ (x : nat), Corelib_Init_Logic_eq (Original_LF__DOT__Induction_LF_Induction_double x) (Nat_add x x)
