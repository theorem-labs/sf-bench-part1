-- Lean 4 translation for le_step and all dependencies

-- Define nat as an inductive type to match Rocq's nat
inductive nat : Type where
  | O : nat
  | S : nat -> nat

-- Alias for S constructor
def S : nat -> nat := nat.S

-- Define le as a DECIDABLE relation using a recursive boolean function
def nat_le : nat -> nat -> Bool
  | nat.O, _ => true
  | nat.S _, nat.O => false
  | nat.S n, nat.S m => nat_le n m

-- Define le as a Prop based on the boolean
def le (n m : nat) : Prop := nat_le n m = true

-- Define lt as S n <= m (matching Rocq's definition)
def lt (n m : nat) : Prop := le (nat.S n) m

-- le_step axiom: forall n m p, n < m -> m <= S p -> n <= p
-- This is Admitted in Original.v, so we axiomatize it
axiom Original_LF_Rel_le__step : forall (n m p : nat), lt n m -> le m (nat.S p) -> le n p
