-- Lean 4 translation of Rocq nat and ev

-- Define nat as an inductive type to match Rocq's nat
inductive nat : Type where
  | O : nat
  | S : nat -> nat

-- Define ev: the evenness predicate on nat
-- Corresponds to:
-- Inductive ev : nat -> Prop :=
--   | ev_0                       : ev 0
--   | ev_SS (n : nat) (H : ev n) : ev (S (S n)).
inductive Original_LF__DOT__IndProp_LF_IndProp_ev : nat -> Prop where
  | ev_0 : Original_LF__DOT__IndProp_LF_IndProp_ev nat.O
  | ev_SS : (n : nat) -> Original_LF__DOT__IndProp_LF_IndProp_ev n -> Original_LF__DOT__IndProp_LF_IndProp_ev (nat.S (nat.S n))
