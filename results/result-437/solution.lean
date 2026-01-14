-- Lean 4 translation for one_not_even' and dependencies
set_option autoImplicit false

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- False (empty type in Prop) - use a custom name to avoid conflict with Lean's False
inductive MyFalse : Prop where

-- Logic.not (negation)
def Logic_not (P : Prop) : Prop := P → MyFalse

-- ev inductive type from EvPlayground
inductive Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev : nat -> Prop where
  | ev_0 : Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev nat.O
  | ev_SS : (n : nat) -> Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev n -> Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev (nat.S (nat.S n))

-- one_not_even': ~ ev 1 (Admitted in Original.v)
-- This is the negation: ev 1 -> False
axiom Original_LF__DOT__IndProp_LF_IndProp_one__not__even' : Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev (S _0) → MyFalse
