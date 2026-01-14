-- Lean translation of Original.LF_DOT_IndPrinciples.LF.IndPrinciples.natlist

-- Define nat to match Coq's nat (which is Nat in Lean)
def nat := Nat

-- Define natlist: a list of natural numbers
inductive Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist : Type where
  | nnil : Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist
  | ncons : nat → Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist → Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist
