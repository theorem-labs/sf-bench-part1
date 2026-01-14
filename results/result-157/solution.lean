-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

-- Standard natural number aliases  
def O : nat := nat.O
def S : nat → nat := nat.S

-- Addition on nat
def Nat_add : nat → nat → nat
  | nat.O, m => m
  | nat.S n, m => nat.S (Nat_add n m)

-- Numeric literals
def _0 : nat := nat.O
def _1 : nat := nat.S nat.O
def _2 : nat := nat.S (nat.S nat.O)
def _3 : nat := nat.S (nat.S (nat.S nat.O))
def _4 : nat := nat.S (nat.S (nat.S (nat.S nat.O)))

-- Equality type (in Prop, not Type, so it becomes SProp when imported)
inductive Original_LF__DOT__ProofObjects_LF_ProofObjects_eq {X : Type} : X → X → Prop where
  | eq_refl : ∀ (x : X), Original_LF__DOT__ProofObjects_LF_ProofObjects_eq x x

-- eq_add' axiom: forall n1 n2 : nat, n1 == n2 -> S n1 == S n2
-- This is Admitted in Original.v so we must declare it as an axiom
axiom Original_LF__DOT__ProofObjects_LF_ProofObjects_eq__add' : 
  ∀ (n1 n2 : nat), Original_LF__DOT__ProofObjects_LF_ProofObjects_eq n1 n2 → 
                   Original_LF__DOT__ProofObjects_LF_ProofObjects_eq (S n1) (S n2)
