-- Lean 4 translation for ev_Even and dependencies

-- nat type
inductive nat : Type where
  | O : nat
  | S : nat -> nat

-- double function
def Original_LF__DOT__Induction_LF_Induction_double : nat -> nat
  | nat.O => nat.O
  | nat.S n' => nat.S (nat.S (Original_LF__DOT__Induction_LF_Induction_double n'))

-- Existential quantifier (specialized to nat -> Prop)
inductive Original_LF__DOT__Logic_LF_Logic_Even_ex (P : nat -> Prop) : Prop where
  | intro : (x : nat) -> P x -> Original_LF__DOT__Logic_LF_Logic_Even_ex P

-- Even definition: exists n, x = double n
-- Using standard Lean Eq here
def Original_LF__DOT__Logic_LF_Logic_Even (x : nat) : Prop :=
  Original_LF__DOT__Logic_LF_Logic_Even_ex (fun n => x = Original_LF__DOT__Induction_LF_Induction_double n)

-- ev inductive type from EvPlayground
inductive Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev : nat -> Prop where
  | ev_0 : Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev nat.O
  | ev_SS : (n : nat) -> Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev n -> Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev (nat.S (nat.S n))

-- ev_Even is Admitted in the original, so we declare it as an axiom
axiom Original_LF__DOT__IndProp_LF_IndProp_ev__Even : (n : nat) -> Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev n -> Original_LF__DOT__Logic_LF_Logic_Even n
