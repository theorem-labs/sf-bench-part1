-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def S : nat → nat := nat.S

-- Use Lean's builtin False directly

-- Logic.not = fun x => x -> False
def Logic_not (x : Prop) : Prop := x → _root_.False

-- Less-than-or-equal relation
inductive le : nat → nat → Prop where
  | le_n (n : nat) : le n n
  | le_S (n m : nat) : le n m → le n (nat.S m)

-- The le_Sn_n theorem is Admitted in Original.v, so we use an axiom here
axiom Original_LF_Rel_le__Sn__n : ∀ (n : nat), le (nat.S n) n → _root_.False
