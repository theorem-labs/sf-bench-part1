-- Lean translation for lia_succeed1 and its dependencies

-- Natural numbers
inductive nat : Type where
| O : nat
| S : nat → nat

-- Aliases for 0 and S
def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Define Nat_add to match Rocq's Nat.add
def Nat_add : nat -> nat -> nat
  | nat.O, m => m
  | nat.S p, m => nat.S (Nat_add p m)

-- Define Nat_mul to match Rocq's Nat.mul
def Nat_mul : nat -> nat -> nat
  | nat.O, _ => nat.O
  | nat.S p, m => Nat_add m (Nat_mul p m)

-- Less than or equal relation
inductive le (n : nat) : nat → Prop where
| le_n : le n n
| le_S : ∀ m : nat, le n m → le n (nat.S m)

-- Less than relation: lt n m = S n <= m
def lt (n m : nat) : Prop := le (nat.S n) m

-- Greater than relation: gt n m = m < n = S m <= n
def gt (n m : nat) : Prop := lt m n

-- The main theorem - lia_succeed1 is Admitted in Original.v
-- n > 0 -> n * 2 > n
axiom Original_LF__DOT__AltAuto_LF_AltAuto_lia__succeed1 :
  ∀ (x : nat), gt x _0 -> gt (Nat_mul x (S (S _0))) x
