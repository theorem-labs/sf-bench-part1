-- Lean 4 translation of Rocq nat and add1

-- Define nat as an inductive type to match Rocq's nat
inductive nat : Type where
  | O : nat
  | S : nat -> nat

-- Define add1 to match Rocq's Original.LF_DOT_ProofObjects.LF.ProofObjects.add1
-- which is: fun n : nat => S n
def Original_LF__DOT__ProofObjects_LF_ProofObjects_add1 (n : nat) : nat := nat.S n
