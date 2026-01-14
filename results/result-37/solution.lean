/-
  Lean translation of le2 from LF.IndPrinciples

  Original Rocq definition:
    Inductive le2 (n:nat) : nat -> Prop :=
      | le2_n : le2 n n
      | le2_S m (H : le2 n m) : le2 n (S m).
-/

-- Define nat to match what Rocq expects
inductive nat : Type where
  | O : nat
  | S : nat → nat

-- The le2 relation: n ≤ m
inductive Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le2 (n : nat) : nat → Prop where
  | le2_n : Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le2 n n
  | le2_S (m : nat) (H : Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le2 n m) : Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le2 n (nat.S m)
