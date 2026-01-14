-- Lean 4 translation for ev_ev__ev and dependencies

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat -> nat

-- Addition on nat
def Nat_add : nat → nat → nat
  | nat.O, m => m
  | nat.S p, m => nat.S (Nat_add p m)

-- ev inductive type from EvPlayground
inductive Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev : nat -> Prop where
  | ev_0 : Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev nat.O
  | ev_SS : (n : nat) -> Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev n -> Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev (nat.S (nat.S n))

-- ev_ev__ev is Admitted in the original, so we declare it as an axiom
axiom Original_LF__DOT__IndProp_LF_IndProp_ev__ev____ev : (n m : nat) -> 
  Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev (Nat_add n m) -> 
  Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev n -> 
  Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev m
