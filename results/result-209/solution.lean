-- Lean 4 translation for nat_ind_tidy (and build_proof)

set_option linter.unusedVariables false
set_option autoImplicit false

-- Natural numbers
inductive nat : Type
| O : nat
| S : nat → nat

-- Aliases for constructors
def _0 : nat := nat.O
def S : nat → nat := nat.S

-- build_proof: the standard nat induction principle
-- Fixpoint build_proof (P : nat -> Prop) (evPO : P 0) (evPS : forall n : nat, P n -> P (S n)) (n : nat) : P n
def Original_LF__DOT__IndPrinciples_LF_IndPrinciples_build__proof
    (P : nat → Prop)
    (evPO : P nat.O)
    (evPS : ∀ n : nat, P n → P (nat.S n))
    (n : nat) : P n :=
  match n with
  | nat.O => evPO
  | nat.S k => evPS k (Original_LF__DOT__IndPrinciples_LF_IndPrinciples_build__proof P evPO evPS k)

-- nat_ind_tidy is defined as build_proof
def Original_LF__DOT__IndPrinciples_LF_IndPrinciples_nat__ind__tidy :=
  Original_LF__DOT__IndPrinciples_LF_IndPrinciples_build__proof
