-- Lean 4 translation of Rocq definitions for bin_nat_bin theorem

-- Use Lean's built-in True (will be exported and become SProp in Rocq)
-- Using a different name to avoid conflicts with Lean's built-in True
def MyTrue : Prop := _root_.True
def True_intro : MyTrue := _root_.True.intro

-- Equality in Prop (will become SProp in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl a

-- Equality for Prop (will become SProp -> SProp -> SProp in Rocq)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

def Corelib_Init_Logic_eq_Prop_refl {A : Prop} (a : A) : Corelib_Init_Logic_eq_Prop a a :=
  Corelib_Init_Logic_eq_Prop.refl a

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Binary numbers
inductive Original_LF__DOT__Induction_LF_Induction_bin : Type where
  | Z : Original_LF__DOT__Induction_LF_Induction_bin
  | B0 : Original_LF__DOT__Induction_LF_Induction_bin → Original_LF__DOT__Induction_LF_Induction_bin
  | B1 : Original_LF__DOT__Induction_LF_Induction_bin → Original_LF__DOT__Induction_LF_Induction_bin

-- bin_to_nat is an axiom (Admitted in Rocq)
axiom Original_LF__DOT__Induction_LF_Induction_bin__to__nat : 
  Original_LF__DOT__Induction_LF_Induction_bin → nat

-- nat_to_bin is an axiom (Admitted in Rocq)
axiom Original_LF__DOT__Induction_LF_Induction_nat__to__bin : 
  nat → Original_LF__DOT__Induction_LF_Induction_bin

-- normalize is an axiom (Admitted in Rocq)
axiom Original_LF__DOT__Induction_LF_Induction_normalize : 
  Original_LF__DOT__Induction_LF_Induction_bin → Original_LF__DOT__Induction_LF_Induction_bin

-- bin_nat_bin theorem (Admitted in Rocq)
-- States: forall b, nat_to_bin (bin_to_nat b) = normalize b
axiom Original_LF__DOT__Induction_LF_Induction_bin__nat__bin : 
  ∀ (b : Original_LF__DOT__Induction_LF_Induction_bin),
    Corelib_Init_Logic_eq 
      (Original_LF__DOT__Induction_LF_Induction_nat__to__bin (Original_LF__DOT__Induction_LF_Induction_bin__to__nat b))
      (Original_LF__DOT__Induction_LF_Induction_normalize b)
