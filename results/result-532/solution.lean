-- Lean translation for silly_presburger_example and dependencies
-- Using the approach from run-1545 for le (via boolean function)
set_option autoImplicit false

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat -> nat

def _0 : nat := nat.O
def S : nat -> nat := nat.S

-- Define Nat_add to match Rocq's Nat.add
def PeanoNat_Nat_add : nat -> nat -> nat
  | nat.O, m => m
  | nat.S p, m => nat.S (PeanoNat_Nat_add p m)

-- Boolean type for le definition
inductive RocqBool : Type where
  | false : RocqBool
  | true : RocqBool

def RocqBool_false : RocqBool := RocqBool.false
def RocqBool_true : RocqBool := RocqBool.true

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

-- Conjunction in Prop
inductive and (A B : Prop) : Prop where
  | conj : A → B → and A B

-- Equality for comparison in the theorem statement (Type version)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality for Prop (needed for Prop isomorphisms)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- True proposition (renamed to avoid conflict with Lean's True)
inductive RocqTrue : Prop where
  | intro : RocqTrue

-- The main axiom (silly_presburger_example is Admitted in Rocq)
axiom Original_LF__DOT__Imp_LF_Imp_AExp_silly__presburger__example :
  ∀ (x x0 x1 x2 : nat),
    and (le (PeanoNat_Nat_add x x0) (PeanoNat_Nat_add x0 x1))
        (Corelib_Init_Logic_eq (PeanoNat_Nat_add x1 (S (S (S _0)))) (PeanoNat_Nat_add x2 (S (S (S _0))))) →
    le x x2
