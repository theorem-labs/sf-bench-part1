-- Lean 4 translation for add_assoc' and its dependencies

set_option autoImplicit false

-- Define nat as an inductive type to match Rocq's nat
inductive nat : Type where
  | O : nat
  | S : nat -> nat

-- Define Nat_add to match Rocq's Nat.add
def Nat_add : nat -> nat -> nat
  | nat.O, m => m
  | nat.S p, m => nat.S (Nat_add p m)

-- Define equality (eq) in Prop
inductive Corelib_Init_Logic_eq {A : Type} (a : A) : A -> Prop where
  | refl : Corelib_Init_Logic_eq a a

-- The axiom for add_assoc' (since the original is Admitted)
axiom Original_LF__DOT__IndPrinciples_LF_IndPrinciples_add__assoc' : 
  ∀ (n m p : nat), Corelib_Init_Logic_eq (Nat_add n (Nat_add m p)) (Nat_add (Nat_add n m) p)
