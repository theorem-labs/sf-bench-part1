-- Lean translation of NatPlayground.nat and pred

inductive Original_LF__DOT__Basics_LF_Basics_NatPlayground_nat : Type where
  | O : Original_LF__DOT__Basics_LF_Basics_NatPlayground_nat
  | S : Original_LF__DOT__Basics_LF_Basics_NatPlayground_nat → Original_LF__DOT__Basics_LF_Basics_NatPlayground_nat

def Original_LF__DOT__Basics_LF_Basics_NatPlayground_pred (n : Original_LF__DOT__Basics_LF_Basics_NatPlayground_nat) : Original_LF__DOT__Basics_LF_Basics_NatPlayground_nat :=
  match n with
  | Original_LF__DOT__Basics_LF_Basics_NatPlayground_nat.O => Original_LF__DOT__Basics_LF_Basics_NatPlayground_nat.O
  | Original_LF__DOT__Basics_LF_Basics_NatPlayground_nat.S n' => n'
