-- Lean 4 translation for and_example and its dependencies

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

-- Define and as a structure matching Rocq's and
structure and (A B : Prop) : Prop where
  intro ::
  left : A
  right : B

-- The main theorem - and_example is Admitted in Original.v
-- 3 + 4 = 7 /\ 2 * 2 = 4
axiom Original_LF__DOT__Logic_LF_Logic_and__example :
  and
    (Corelib_Init_Logic_eq (Nat_add (S (S (S _0))) (S (S (S (S _0))))) (S (S (S (S (S (S (S _0))))))))
    (Corelib_Init_Logic_eq (Nat_mul (S (S _0)) (S (S _0))) (S (S (S (S _0)))))
