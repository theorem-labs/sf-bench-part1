-- Lean 4 translation for trans_example1 and its dependencies
set_option autoImplicit false

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat -> nat

-- Define Nat_add to match Rocq's Nat.add
def Nat_add : nat -> nat -> nat
  | nat.O, m => m
  | nat.S p, m => nat.S (Nat_add p m)

-- Define Nat_mul to match Rocq's Nat.mul
def Nat_mul : nat -> nat -> nat
  | nat.O, _ => nat.O
  | nat.S p, m => Nat_add m (Nat_mul p m)

-- Aliases for 0 and S
def _0 : nat := nat.O
def S : nat -> nat := nat.S

-- Boolean type for le definition
inductive RocqBool : Type where
  | false : RocqBool
  | true : RocqBool

def Bool_false : RocqBool := RocqBool.false
def Bool_true : RocqBool := RocqBool.true

-- nat_le: boolean less-than-or-equal
def nat_le : nat → nat → RocqBool
  | nat.O, _ => RocqBool.true
  | nat.S _, nat.O => RocqBool.false
  | nat.S n, nat.S m => nat_le n m

-- Equality type (will become SProp Eq in Rocq)
inductive RocqEq {A : Type} : A → A → Prop where
  | refl (a : A) : RocqEq a a

def Eq_refl (A : Type) (a : A) : RocqEq a a := RocqEq.refl a

-- le as Prop based on boolean
def le (n m : nat) : Prop := RocqEq (nat_le n m) RocqBool.true

-- trans_example1: Admitted in Original.v, so we use an axiom
-- forall a b c d, a <= b + b * c -> (1 + c) * b <= d -> a <= d
axiom Original_LF__DOT__AltAuto_LF_AltAuto_trans__example1 :
  ∀ (a b c d : nat),
    le a (Nat_add b (Nat_mul b c)) →
    le (Nat_mul (Nat_add (S _0) c) b) d →
    le a d
