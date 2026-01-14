-- Lean 4 translation for specialize_example and its dependencies

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

-- True in Prop (also aliased as "True" for export)
inductive PTrue : Prop where
  | intro : PTrue

-- We use a namespace trick to export "True" 
namespace Exports
  def True : Prop := PTrue
end Exports

-- Define equality in Prop (becomes SProp when imported)
inductive Corelib_Init_Logic_eq {A : Type} : A -> A -> Prop where
  | refl : (a : A) -> Corelib_Init_Logic_eq a a

-- Define equality in Prop for Prop-typed values (also becomes SProp when imported)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A -> A -> Prop where
  | refl : (a : A) -> Corelib_Init_Logic_eq_Prop a a

-- The main theorem - specialize_example is Admitted in Original.v
-- forall n, (forall m, m*n = 0) -> n = 0
axiom Original_LF__DOT__Tactics_LF_Tactics_specialize__example :
  forall (n : nat),
    (forall (m : nat), Corelib_Init_Logic_eq (Nat_mul m n) _0) ->
    Corelib_Init_Logic_eq n _0
