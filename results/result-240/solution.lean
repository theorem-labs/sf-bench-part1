-- Lean 4 translation of Rocq definitions for plus_lt isomorphism

-- Define nat as an inductive type to match Rocq's nat
inductive nat : Type where
  | O : nat
  | S : nat -> nat

-- Define Nat_add to match Rocq's Nat.add
def Nat_add : nat -> nat -> nat
  | nat.O, m => m
  | nat.S p, m => nat.S (Nat_add p m)

-- Define le (less than or equal) to match Rocq's le
inductive le : nat -> nat -> Prop where
  | le_n : forall n : nat, le n n
  | le_S : forall n m : nat, le n m -> le n (nat.S m)

-- Define lt in terms of le
def lt (n m : nat) : Prop := le (nat.S n) m

-- Define and in SProp to match Rocq's and (which becomes SProp after import)
structure and (A B : Prop) : Prop where
  intro ::
  left : A
  right : B

-- Define the plus_lt axiom
axiom Original_LF__DOT__IndProp_LF_IndProp_plus__lt :
  forall (n1 n2 m : nat), lt (Nat_add n1 n2) m -> and (lt n1 m) (lt n2 m)
