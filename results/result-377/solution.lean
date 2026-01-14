-- Lean 4 translation for and_example3 and its dependencies

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

-- True in Prop
inductive PTrue : Prop where
  | intro : PTrue

-- Alias True_alias -> PTrue (we will rename this in the .out file)
abbrev True_alias : Prop := PTrue

-- Define equality in Prop (becomes SProp when imported) for Type
inductive Corelib_Init_Logic_eq {A : Type} : A -> A -> Prop where
  | refl : (a : A) -> Corelib_Init_Logic_eq a a

-- Define equality in Prop for Prop (becomes SProp when imported)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A -> A -> Prop where
  | refl : (a : A) -> Corelib_Init_Logic_eq_Prop a a

-- The main theorem - and_example3 is Admitted in Original.v
-- forall n m : nat, n + m = 0 -> n * m = 0
axiom Original_LF__DOT__Logic_LF_Logic_and__example3 :
  forall (n m : nat), Corelib_Init_Logic_eq (Nat_add n m) _0 -> Corelib_Init_Logic_eq (Nat_mul n m) _0
