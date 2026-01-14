-- Lean 4 translation of Rocq nat, Nat.add, True, eq, and add_assoc''

set_option autoImplicit false

-- Define nat as an inductive type to match Rocq's nat
inductive nat : Type where
  | O : nat
  | S : nat -> nat

-- Define Nat_add to match Rocq's Nat.add
def Nat_add : nat -> nat -> nat
  | nat.O, m => m
  | nat.S p, m => nat.S (Nat_add p m)

-- Define MyTrue to match Rocq's True (renamed to avoid collision with Lean's True)
inductive MyTrue : Prop where
  | intro : MyTrue

-- Define eq to match Rocq's Corelib.Init.Logic.eq
inductive Corelib_Init_Logic_eq {A : Type} (a : A) : A -> Prop where
  | refl : Corelib_Init_Logic_eq a a

-- The main theorem add_assoc'' is Admitted in Original.v, so we use an axiom
axiom Original_LF__DOT__Induction_LF_Induction_add__assoc'' : 
  ∀ (n m p : nat), Corelib_Init_Logic_eq (Nat_add n (Nat_add m p)) (Nat_add (Nat_add n m) p)
