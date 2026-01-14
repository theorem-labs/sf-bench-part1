set_option autoImplicit false

-- Define mybool type to match Rocq's bool
inductive mybool : Type where
  | true : mybool
  | false : mybool

-- Define mynat type to match Rocq's nat
inductive mynat : Type where
  | O : mynat
  | S : mynat → mynat

-- True in Prop (becomes SProp when imported)
inductive PTrue : Prop where
  | intro : PTrue

-- Equality in Prop for Type arguments (becomes SProp when imported)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality in Prop for Prop arguments (becomes SProp when imported)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- Definitions using our types
def mytrue : mybool := mybool.true
def my0 : mynat := mynat.O
def myTrue : Prop := PTrue

-- Define leb (less-than-or-equal boolean) using recursion
def PeanoNat_Nat_leb : mynat → mynat → mybool :=
  fun n m =>
    match n with
    | mynat.O => mybool.true
    | mynat.S n' =>
      match m with
      | mynat.O => mybool.false
      | mynat.S m' => PeanoNat_Nat_leb n' m'

-- The foo axiom: forall n, 0 <=? n = true
-- This is an Admitted lemma in the original Rocq code
axiom Original_LF__DOT__Imp_LF_Imp_AExp_foo : ∀ x : mynat, Corelib_Init_Logic_eq (PeanoNat_Nat_leb my0 x) mytrue
