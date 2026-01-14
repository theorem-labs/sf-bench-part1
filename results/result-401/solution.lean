-- Lean 4 translation for mult_n_1 and its dependencies

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

-- Aliases for 0 and S
def _0 : nat := nat.O
def S : nat -> nat := nat.S

-- True in Prop - using a custom name to avoid conflict with built-in True
inductive PTrue : Prop where
  | intro : PTrue

-- Define True as an alias for export
def True' : Prop := PTrue
def True'_intro : True' := PTrue.intro

-- Define equality in Prop (becomes SProp when imported) - for Type
inductive Corelib_Init_Logic_eq {A : Type} : A -> A -> Prop where
  | refl : (a : A) -> Corelib_Init_Logic_eq a a

-- Define equality in Prop (becomes SProp when imported) - for Prop
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A -> A -> Prop where
  | refl : (a : A) -> Corelib_Init_Logic_eq_Prop a a

-- The main theorem - mult_n_1 is Admitted in Original.v
-- forall p : nat, p * 1 = p
axiom Original_LF__DOT__Basics_LF_Basics_mult__n__1 :
  forall (p : nat), Corelib_Init_Logic_eq (Nat_mul p (S _0)) p
