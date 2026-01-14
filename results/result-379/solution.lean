-- Lean 4 translation for mult_1_l and its dependencies

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

-- Define equality in Prop (becomes SProp when imported)
inductive Corelib_Init_Logic_eq {A : Type} : A -> A -> Prop where
  | refl : (a : A) -> Corelib_Init_Logic_eq a a

-- Define equality for Prop (becomes SProp when imported)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A -> A -> Prop where
  | refl : (a : A) -> Corelib_Init_Logic_eq_Prop a a

-- The main theorem - mult_1_l is Admitted in Original.v
-- forall n:nat, 1 * n = n
-- 1 * n = S 0 * n = Nat_add n (Nat_mul 0 n) = Nat_add n 0 = n? No wait...
-- S 0 * n in our definition is Nat_mul (S 0) n = Nat_add n (Nat_mul 0 n) = Nat_add n 0
-- But Nat_add n 0 = n only when we reduce it (n + 0 = n doesn't reduce by definition)
-- So we need axiom for this
axiom Original_LF__DOT__Induction_LF_Induction_mult__1__l :
  (x : nat) -> Corelib_Init_Logic_eq (Nat_mul (S _0) x) x
