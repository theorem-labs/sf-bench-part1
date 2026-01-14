-- Lean 4 translation of Rocq nat and plus'

-- Define nat as an inductive type to match Rocq's nat
inductive nat : Type where
  | O : nat
  | S : nat -> nat

-- Define plus' to match Rocq's LF.Basics.plus'
def Original_LF__DOT__Basics_LF_Basics_plus' : nat -> nat -> nat
  | nat.O, m => m
  | nat.S n', m => nat.S (Original_LF__DOT__Basics_LF_Basics_plus' n' m)
