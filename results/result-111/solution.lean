-- Lean 4 translation of Rocq nat, le, and ge

-- Define nat as an inductive type to match Rocq's nat
inductive nat : Type where
  | O : nat
  | S : nat -> nat

-- Define le (less than or equal) as an inductive type to match Rocq's LF.IndProp.le
-- Original Rocq definition:
-- Inductive le : nat -> nat -> Prop :=
--   | le_n (n : nat)   : le n n
--   | le_S (n m : nat) : le n m -> le n (S m).
inductive Original_LF__DOT__IndProp_LF_IndProp_le : nat -> nat -> Prop where
  | le_n (n : nat) : Original_LF__DOT__IndProp_LF_IndProp_le n n
  | le_S (n m : nat) : Original_LF__DOT__IndProp_LF_IndProp_le n m -> Original_LF__DOT__IndProp_LF_IndProp_le n (nat.S m)

-- Define ge (greater than or equal) as le with swapped arguments
-- Original Rocq definition: Definition ge (m n : nat) : Prop := le n m.
def Original_LF__DOT__IndProp_LF_IndProp_ge (m n : nat) : Prop := Original_LF__DOT__IndProp_LF_IndProp_le n m
