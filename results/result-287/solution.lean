-- Lean 4 translation for mult_plus_distr_r and its dependencies

-- Define nat as an inductive type to match Rocq's nat
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

-- True in Prop (becomes SProp when imported to Rocq)
inductive PTrue : Prop where
  | intro : PTrue

-- Define equality in Prop (becomes SProp when imported)
inductive Corelib_Init_Logic_eq {A : Type} : A -> A -> Prop where
  | refl : (a : A) -> Corelib_Init_Logic_eq a a

-- Define equality in Prop for Props (becomes SProp -> SProp -> SProp when imported)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A -> A -> Prop where
  | refl : (a : A) -> Corelib_Init_Logic_eq_Prop a a

-- The main theorem - mult_plus_distr_r is Admitted in Original.v
-- forall n m p : nat, (n + m) * p = (n * p) + (m * p)
axiom Original_LF__DOT__Induction_LF_Induction_mult__plus__distr__r :
  forall (n m p : nat), Corelib_Init_Logic_eq (Nat_mul (Nat_add n m) p) (Nat_add (Nat_mul n p) (Nat_mul m p))
