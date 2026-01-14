-- Lean 4 translation for ev_plus4 and dependencies
set_option autoImplicit false

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Addition on nat
def Nat_add : nat → nat → nat
  | nat.O, m => m
  | nat.S n, m => nat.S (Nat_add n m)

-- ev inductive type from EvPlayground
inductive Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev : nat -> Prop where
  | ev_0 : Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev nat.O
  | ev_SS : (n : nat) -> Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev n -> Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev (nat.S (nat.S n))

-- ev_plus4: ev n -> ev (4 + n) (Admitted in Original.v, so we use an axiom)
-- 4 = S (S (S (S 0)))
axiom Original_LF__DOT__IndProp_LF_IndProp_ev__plus4 : 
  ∀ (x : nat), Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev x → 
    Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev (Nat_add (S (S (S (S _0)))) x)
