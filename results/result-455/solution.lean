-- Define bool type to match Rocq's
inductive Mybool : Type where
  | true : Mybool
  | false : Mybool

-- Define nat type to match Rocq's
inductive Mynat : Type where
  | O : Mynat
  | S : Mynat → Mynat

-- Define true as a bool value
def Mytrue : Mybool := Mybool.true

-- Define 0 as a nat value
def My0 : Mynat := Mynat.O

-- Define leb (less-than-or-equal boolean) using recursion
def PeanoNat_Nat_leb : Mynat → Mynat → Mybool :=
  fun n m =>
    match n with
    | Mynat.O => Mybool.true
    | Mynat.S n' =>
      match m with
      | Mynat.O => Mybool.false
      | Mynat.S m' => PeanoNat_Nat_leb n' m'

-- True in Prop (becomes SProp when imported)
inductive MyTrue : Prop where
  | intro : MyTrue

-- Equality in Prop for Type arguments (becomes SProp when imported)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality in Prop for Prop arguments (becomes SProp when imported)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- The foo' axiom: forall n, 0 <=? n = true
-- This is an Admitted lemma in the original Rocq code
axiom Original_LF__DOT__Imp_LF_Imp_AExp_foo' : ∀ x : Mynat, Corelib_Init_Logic_eq (PeanoNat_Nat_leb My0 x) Mytrue
