-- True in Prop
inductive PTrue : Prop where
  | intro : PTrue

-- Export True as an alias - but Lean already has True, so we work around it
-- by putting it in a namespace
namespace Solution
  def True : Prop := PTrue
end Solution

-- Equality in Prop (so it becomes SProp when imported)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

-- The silly1 axiom: forall n m : nat, n = m -> n = m
-- This is Admitted in the Original.v so we declare it as an axiom
axiom Original_LF__DOT__Tactics_LF_Tactics_silly1 : 
  ∀ (n m : nat), Corelib_Init_Logic_eq n m → Corelib_Init_Logic_eq n m
