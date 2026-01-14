-- Lean 4 translation for is_three

-- Define nat as an inductive type to match Rocq's nat
inductive nat : Type where
  | O : nat
  | S : nat -> nat

-- Define 3 as S (S (S O))
def three : nat := nat.S (nat.S (nat.S nat.O))

-- is_three n means n = 3 (using Lean's built-in equality which is Prop)
def Original_LF__DOT__Logic_LF_Logic_is__three (n : nat) : Prop :=
  n = three
