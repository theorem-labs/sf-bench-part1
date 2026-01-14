-- Lean 4 translation for le_Sn_n and dependencies
set_option autoImplicit false

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Boolean type for le definition  
inductive RBool : Type where
  | false : RBool
  | true : RBool

def Bool_false : RBool := RBool.false
def Bool_true : RBool := RBool.true

-- nat_le: boolean less-than-or-equal
def nat_le : nat → nat → RBool
  | nat.O, _ => RBool.true
  | nat.S _, nat.O => RBool.false  
  | nat.S n, nat.S m => nat_le n m

-- Equality type (will become SProp Eq in Rocq)
inductive REq {A : Type} : A → A → Prop where
  | refl (a : A) : REq a a

def Eq_refl {A : Type} (a : A) : REq a a := REq.refl a

-- le as Prop based on boolean
def le (n m : nat) : Prop := REq (nat_le n m) RBool.true

-- RFalse (empty type in Prop) - will be renamed to False in Imported.out
inductive RFalse : Prop where

-- Logic.not (negation)
def Logic_not (P : Prop) : Prop := P → RFalse

-- le_Sn_n: Admitted in Original.v, so we use an axiom
axiom Original_LF_Rel_le__Sn__n : ∀ (n : nat), le (S n) n → RFalse
