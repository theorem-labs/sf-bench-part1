-- Lean 4 translation for mul_0_r'' and P_m0r

-- Define nat as an inductive type to match Rocq's nat
inductive nat : Type where
  | O : nat
  | S : nat -> nat

-- Define nat addition 
def nat_add : nat -> nat -> nat
  | nat.O, m => m
  | nat.S p, m => nat.S (nat_add p m)

-- Define nat multiplication to match Rocq's Nat.mul
def nat_mul : nat -> nat -> nat
  | nat.O, _ => nat.O
  | nat.S p, m => nat_add (nat_mul p m) m

-- P_m0r: n * 0 = 0
def Original_LF__DOT__IndPrinciples_LF_IndPrinciples_P__m0r (n : nat) : Prop :=
  nat_mul n nat.O = nat.O

-- mul_0_r'' is an axiom (admitted theorem in Rocq)
axiom Original_LF__DOT__IndPrinciples_LF_IndPrinciples_mul__0__r'' : 
  ∀ (n : nat), Original_LF__DOT__IndPrinciples_LF_IndPrinciples_P__m0r n
