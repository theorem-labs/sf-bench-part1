-- Translation of natlist' from Rocq to Lean 4

-- We need to define nat to match Rocq's nat
inductive nat : Type where
  | O : nat
  | S : nat → nat

-- Define natlist' matching the Rocq definition
inductive Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist' : Type where
  | nnil' : Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist'
  | nsnoc : Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist' → nat → Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist'
