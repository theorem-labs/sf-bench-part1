-- Lean 4 translation of definitions for test_bin_incr5
set_option autoImplicit false

-- Equality for Type arguments (so it becomes SProp when imported)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality for Prop arguments (will become SProp eq for SProp arguments)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Define Nat_add to match Rocq's Nat.add
def Nat_add : nat -> nat -> nat
  | nat.O, m => m
  | nat.S p, m => nat.S (Nat_add p m)

-- bin type from LF.Basics module
inductive Original_LF__DOT__Basics_LF_Basics_bin : Type where
  | Z : Original_LF__DOT__Basics_LF_Basics_bin
  | B0 : Original_LF__DOT__Basics_LF_Basics_bin -> Original_LF__DOT__Basics_LF_Basics_bin
  | B1 : Original_LF__DOT__Basics_LF_Basics_bin -> Original_LF__DOT__Basics_LF_Basics_bin

-- bin constructors as definitions
def Original_LF__DOT__Basics_LF_Basics_Z : Original_LF__DOT__Basics_LF_Basics_bin :=
  Original_LF__DOT__Basics_LF_Basics_bin.Z

def Original_LF__DOT__Basics_LF_Basics_B0 : Original_LF__DOT__Basics_LF_Basics_bin -> Original_LF__DOT__Basics_LF_Basics_bin :=
  Original_LF__DOT__Basics_LF_Basics_bin.B0

def Original_LF__DOT__Basics_LF_Basics_B1 : Original_LF__DOT__Basics_LF_Basics_bin -> Original_LF__DOT__Basics_LF_Basics_bin :=
  Original_LF__DOT__Basics_LF_Basics_bin.B1

-- bin_to_nat is an axiom (Admitted in Original.v)
axiom Original_LF__DOT__Basics_LF_Basics_bin__to__nat : Original_LF__DOT__Basics_LF_Basics_bin -> nat

-- incr is an axiom (Admitted in Original.v)
axiom Original_LF__DOT__Basics_LF_Basics_incr : Original_LF__DOT__Basics_LF_Basics_bin -> Original_LF__DOT__Basics_LF_Basics_bin

-- test_bin_incr5 is an axiom (Admitted in Original.v)
-- It states: bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z)
axiom Original_LF__DOT__Basics_LF_Basics_test__bin__incr5 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Basics_LF_Basics_bin__to__nat
       (Original_LF__DOT__Basics_LF_Basics_incr (Original_LF__DOT__Basics_LF_Basics_B1 Original_LF__DOT__Basics_LF_Basics_Z)))
    (Nat_add (S _0) (Original_LF__DOT__Basics_LF_Basics_bin__to__nat (Original_LF__DOT__Basics_LF_Basics_B1 Original_LF__DOT__Basics_LF_Basics_Z)))
