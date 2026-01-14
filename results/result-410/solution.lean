-- Lean 4 translation for plus_is_O and its dependencies

-- Define nat as an inductive type to match Rocq's nat
inductive nat : Type where
  | O : nat
  | S : nat -> nat

-- Define Nat_add to match Rocq's Nat.add
def Nat_add : nat -> nat -> nat
  | nat.O, m => m
  | nat.S p, m => nat.S (Nat_add p m)

-- Aliases for 0 and S
def _0 : nat := nat.O

-- True in Prop
inductive PTrue : Prop where
  | intro : PTrue

-- Create a namespace to shadow True
namespace MyDefs
def True : Prop := PTrue
end MyDefs

export MyDefs (True)

-- Define equality in Prop (becomes SProp when imported)
inductive Corelib_Init_Logic_eq {A : Type} : A -> A -> Prop where
  | refl : (a : A) -> Corelib_Init_Logic_eq a a

-- Define equality over Prop (becomes SProp -> SProp -> SProp when imported)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A -> A -> Prop where
  | refl : (a : A) -> Corelib_Init_Logic_eq_Prop a a

-- Define and as a structure matching Rocq's and
structure and (A B : Prop) : Prop where
  intro ::
  left : A
  right : B

-- plus_is_O is Admitted in Original.v, so we translate it as an axiom
-- forall n m : nat, n + m = 0 -> n = 0 /\ m = 0
axiom Original_LF__DOT__Logic_LF_Logic_plus__is__O :
  forall (n m : nat),
    Corelib_Init_Logic_eq (Nat_add n m) _0 -> and (Corelib_Init_Logic_eq n _0) (Corelib_Init_Logic_eq m _0)
