-- Lean 4 translation for LF.Basics module definitions

namespace Imported
-- True in Prop (will become SProp in Rocq)
-- Use a namespace to avoid conflict with Lean's built-in True
inductive True : Prop where
  | intro : True
end Imported

-- Equality in Prop for Type arguments (so it becomes SProp when imported)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality in Prop for Prop arguments (will become SProp -> SProp -> SProp when imported)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- bin type from LF.Basics
inductive Original_LF__DOT__Basics_LF_Basics_bin : Type where
  | Z : Original_LF__DOT__Basics_LF_Basics_bin
  | B0 : Original_LF__DOT__Basics_LF_Basics_bin -> Original_LF__DOT__Basics_LF_Basics_bin
  | B1 : Original_LF__DOT__Basics_LF_Basics_bin -> Original_LF__DOT__Basics_LF_Basics_bin

-- Z constructor
def Original_LF__DOT__Basics_LF_Basics_Z : Original_LF__DOT__Basics_LF_Basics_bin :=
  Original_LF__DOT__Basics_LF_Basics_bin.Z

-- B0 constructor  
def Original_LF__DOT__Basics_LF_Basics_B0 : Original_LF__DOT__Basics_LF_Basics_bin -> Original_LF__DOT__Basics_LF_Basics_bin :=
  Original_LF__DOT__Basics_LF_Basics_bin.B0

-- B1 constructor
def Original_LF__DOT__Basics_LF_Basics_B1 : Original_LF__DOT__Basics_LF_Basics_bin -> Original_LF__DOT__Basics_LF_Basics_bin :=
  Original_LF__DOT__Basics_LF_Basics_bin.B1

-- incr is an Admitted axiom in the original, so we use an axiom here
axiom Original_LF__DOT__Basics_LF_Basics_incr : Original_LF__DOT__Basics_LF_Basics_bin -> Original_LF__DOT__Basics_LF_Basics_bin

-- test_bin_incr3 is an Admitted example in the original
axiom Original_LF__DOT__Basics_LF_Basics_test__bin__incr3 : 
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__Basics_LF_Basics_incr (Original_LF__DOT__Basics_LF_Basics_B1 (Original_LF__DOT__Basics_LF_Basics_B1 Original_LF__DOT__Basics_LF_Basics_Z)))
    (Original_LF__DOT__Basics_LF_Basics_B0 (Original_LF__DOT__Basics_LF_Basics_B0 (Original_LF__DOT__Basics_LF_Basics_B1 Original_LF__DOT__Basics_LF_Basics_Z)))
