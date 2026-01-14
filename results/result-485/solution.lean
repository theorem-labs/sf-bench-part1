-- Lean 4 translation for sat_ex2 and its dependencies

set_option autoImplicit false

-- Define nat as an inductive type to match Rocq's nat
inductive nat : Type where
  | O : nat
  | S : nat -> nat

-- Define _0 and S as aliases
def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Define Nat_add to match Rocq's Nat.add
def Nat_add : nat -> nat -> nat
  | nat.O, m => m
  | nat.S p, m => nat.S (Nat_add p m)

-- Define Nat_sub to match Rocq's Nat.sub (truncated subtraction)
def Nat_sub : nat -> nat -> nat
  | n, nat.O => n
  | nat.O, nat.S _ => nat.O
  | nat.S n, nat.S m => Nat_sub n m

-- True proposition (PTrue in Prop, will become SProp after import)
inductive PTrue : Prop where
  | intro : PTrue

-- We need to export "True" for the checker, but True is a keyword in Lean
-- Use a namespace approach
namespace MyDefs
def True : Prop := PTrue
end MyDefs

-- Equality (in Prop to match Rocq)
inductive Corelib_Init_Logic_eq {A : Type} (a : A) : A -> Prop where
  | refl : Corelib_Init_Logic_eq a a

-- sat_ex2 is Admitted in Original.v: forall (n : nat), 1 - 1 + n + 1 = 1 + n
-- We declare it as an axiom
axiom Original_LF__DOT__AltAuto_LF_AltAuto_sat__ex2 :
  forall (n : nat),
    Corelib_Init_Logic_eq
      (Nat_add (Nat_add (Nat_sub (S _0) (S _0)) n) (S _0))
      (Nat_add (S _0) n)
