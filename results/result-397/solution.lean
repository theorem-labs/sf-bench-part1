-- Lean 4 translation for mult_0_plus' and its dependencies

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

-- Alias for 0
def _0 : nat := nat.O

-- PTrue in Prop (will become SProp when imported to Rocq)
inductive PTrue : Prop where
  | intro : PTrue

-- MyTrue as an alias to PTrue (will be renamed to True in the output)
def MyTrue : Prop := PTrue

-- Define equality in Prop for Type (becomes SProp when imported)
inductive Corelib_Init_Logic_eq {A : Type} : A -> A -> Prop where
  | refl : (a : A) -> Corelib_Init_Logic_eq a a

-- Define equality in Prop for Prop (becomes SProp when imported)  
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A -> A -> Prop where
  | refl : (a : A) -> Corelib_Init_Logic_eq_Prop a a

-- The main theorem - mult_0_plus' is Admitted in Original.v
-- forall n m : nat, (n + 0 + 0) * m = n * m
axiom Original_LF__DOT__Induction_LF_Induction_mult__0__plus' :
  forall (n m : nat), Corelib_Init_Logic_eq (Nat_mul (Nat_add (Nat_add n _0) _0) m) (Nat_mul n m)
