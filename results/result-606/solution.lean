-- Lean 4 translation of Rocq definitions for bin_to_nat_pres_incr

-- Use Lean's built-in True (will be exported and become SProp in Rocq)
-- Using a different name to avoid conflicts with Lean's built-in True
def MyTrue : Prop := _root_.True
def True_intro : MyTrue := _root_.True.intro

-- Equality in Prop (will become SProp in Rocq) - for Type arguments
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl a

-- Equality for Prop arguments (becomes SProp equality on SProp arguments in Rocq)
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

-- Addition for nat
def Nat_add : nat → nat → nat
  | nat.O, m => m
  | nat.S p, m => nat.S (Nat_add p m)

-- Binary numbers
inductive Original_LF__DOT__Induction_LF_Induction_bin : Type where
  | Z : Original_LF__DOT__Induction_LF_Induction_bin
  | B0 : Original_LF__DOT__Induction_LF_Induction_bin → Original_LF__DOT__Induction_LF_Induction_bin
  | B1 : Original_LF__DOT__Induction_LF_Induction_bin → Original_LF__DOT__Induction_LF_Induction_bin

-- These are axioms in Original.v (admitted fixpoints)
axiom Original_LF__DOT__Induction_LF_Induction_incr : 
  Original_LF__DOT__Induction_LF_Induction_bin → Original_LF__DOT__Induction_LF_Induction_bin

axiom Original_LF__DOT__Induction_LF_Induction_bin__to__nat : 
  Original_LF__DOT__Induction_LF_Induction_bin → nat

-- The main theorem (also an axiom in Original.v)
axiom Original_LF__DOT__Induction_LF_Induction_bin__to__nat__pres__incr :
  ∀ (x : Original_LF__DOT__Induction_LF_Induction_bin),
    Corelib_Init_Logic_eq 
      (Original_LF__DOT__Induction_LF_Induction_bin__to__nat (Original_LF__DOT__Induction_LF_Induction_incr x))
      (Nat_add (S _0) (Original_LF__DOT__Induction_LF_Induction_bin__to__nat x))
