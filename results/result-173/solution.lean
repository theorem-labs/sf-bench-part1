-- Lean translation of nat, plus, mult, and exp

-- Define nat as an alias for Nat to ensure proper export naming
inductive nat : Type where
  | O : nat
  | S : nat → nat

-- Define plus (addition) on nat
def Original_LF__DOT__Basics_LF_Basics_plus : nat → nat → nat
  | nat.O, m => m
  | nat.S n', m => nat.S (Original_LF__DOT__Basics_LF_Basics_plus n' m)

-- Define mult (multiplication) on nat
def Original_LF__DOT__Basics_LF_Basics_mult : nat → nat → nat
  | nat.O, _ => nat.O
  | nat.S n', m => Original_LF__DOT__Basics_LF_Basics_plus m (Original_LF__DOT__Basics_LF_Basics_mult n' m)

-- Define exp (exponentiation) on nat
-- exp base power = base ^ power
def Original_LF__DOT__Basics_LF_Basics_exp : nat → nat → nat
  | base, nat.O => nat.S nat.O  -- base^0 = 1
  | base, nat.S p => Original_LF__DOT__Basics_LF_Basics_mult base (Original_LF__DOT__Basics_LF_Basics_exp base p)
