-- Lean 4 translation for not_even_1001' and its dependencies

-- nat type
inductive nat : Type where
  | O : nat
  | S : nat -> nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- double function
def Original_LF__DOT__Induction_LF_Induction_double : nat -> nat
  | nat.O => nat.O
  | nat.S n' => nat.S (nat.S (Original_LF__DOT__Induction_LF_Induction_double n'))

-- Custom Eq type for the existential (renamed to avoid conflict)
inductive MyEq (A : Type) : A -> A -> Prop where
  | refl : (x : A) -> MyEq A x x

-- Existential quantifier (specialized to nat -> Prop)
inductive Original_LF__DOT__Logic_LF_Logic_Even_ex (P : nat -> Prop) : Prop where
  | intro : (x : nat) -> P x -> Original_LF__DOT__Logic_LF_Logic_Even_ex P

-- Even definition: exists n, x = double n
def Original_LF__DOT__Logic_LF_Logic_Even (x : nat) : Prop :=
  Original_LF__DOT__Logic_LF_Logic_Even_ex (fun n => MyEq nat x (Original_LF__DOT__Induction_LF_Induction_double n))

-- False type - named MyFalse to avoid conflict, will be renamed in .out file
inductive MyFalse : Prop where

-- Logic.not
def Logic_not (P : Prop) : Prop := P → MyFalse

-- Helper to build 998 = S^998(0) using iteration
-- We build it as S^998(0) which matches what iterate1 produces
def iterate (f : nat → nat) : Nat → nat → nat
  | 0, x => x
  | n+1, x => f (iterate f n x)

-- Build 998 by computing it
def n998 : nat := iterate nat.S 998 nat.O

-- n1001 = S(S(S(n998))) to match the expected representation S(S(S(iterate1 S 998 0)))
def n1001 : nat := nat.S (nat.S (nat.S n998))

-- not_even_1001' is Admitted in Original.v, so we declare it as an axiom
axiom Original_LF__DOT__Logic_LF_Logic_not__even__1001' : Original_LF__DOT__Logic_LF_Logic_Even n1001 → MyFalse
