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

-- four' : 2 + 2 == 1 + 3 := eq_refl 4
-- 2 + 2 = S(S(O)) + S(S(O)) = 4
-- 1 + 3 = S(O) + S(S(S(O))) = 4
def Original_LF__DOT__ProofObjects_LF_ProofObjects_four' : 
  Original_LF__DOT__ProofObjects_LF_ProofObjects_eq 
    (Nat_add (S (S O)) (S (S O))) 
    (Nat_add (S O) (S (S (S O)))) :=
  Original_LF__DOT__ProofObjects_LF_ProofObjects_eq.eq_refl _4
