-- Lean translation for nat_bin_nat theorem and dependencies

-- Define nat as an alias for Lean's Nat to get exported correctly
def nat := Nat

-- Define True (will become SProp in Rocq)
def MyTrue : Prop := _root_.True
def True_intro : MyTrue := _root_.True.intro

-- Equality in Prop (will become SProp in Rocq)
-- Using an inductive definition to get proper Corelib_Init_Logic_eq export
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl a

-- Equality for Prop (needed for the Prop version)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

def Corelib_Init_Logic_eq_Prop_refl {A : Prop} (a : A) : Corelib_Init_Logic_eq_Prop a a :=
  Corelib_Init_Logic_eq_Prop.refl a

-- Define the bin type (binary numbers)
inductive Original_LF__DOT__Induction_LF_Induction_bin : Type where
  | Z : Original_LF__DOT__Induction_LF_Induction_bin
  | B0 : Original_LF__DOT__Induction_LF_Induction_bin -> Original_LF__DOT__Induction_LF_Induction_bin
  | B1 : Original_LF__DOT__Induction_LF_Induction_bin -> Original_LF__DOT__Induction_LF_Induction_bin

-- bin_to_nat is an axiom (Admitted in Rocq)
axiom Original_LF__DOT__Induction_LF_Induction_bin__to__nat : Original_LF__DOT__Induction_LF_Induction_bin -> nat

-- nat_to_bin is an axiom (Admitted in Rocq)
axiom Original_LF__DOT__Induction_LF_Induction_nat__to__bin : nat -> Original_LF__DOT__Induction_LF_Induction_bin

-- nat_bin_nat theorem (Admitted in Rocq)
-- States: forall n, bin_to_nat (nat_to_bin n) = n
axiom Original_LF__DOT__Induction_LF_Induction_nat__bin__nat : 
  ∀ (n : nat), Corelib_Init_Logic_eq (Original_LF__DOT__Induction_LF_Induction_bin__to__nat (Original_LF__DOT__Induction_LF_Induction_nat__to__bin n)) n
