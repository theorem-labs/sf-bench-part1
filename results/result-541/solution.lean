-- Lean 4 translation for not_true_iff_false and all dependencies
set_option autoImplicit false

-- True (unit type in Prop) - define with prefixed name to avoid Lean conflict
inductive RocqTrue : Prop where
  | intro : RocqTrue

-- False (empty type in Prop)  
inductive RocqFalse : Prop where

-- Logic.not (negation)
def Logic_not (P : Prop) : Prop := P → RocqFalse

-- iff (biconditional)
structure iff (A B : Prop) : Prop where
  mp : A → B
  mpr : B → A

-- Equality in Prop (for Type)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality in Prop (for Prop)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- Boolean type
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- not_true_iff_false: b <> true <-> b = false
-- This is Admitted in Original.v, so we use axiom
axiom Original_LF__DOT__Logic_LF_Logic_not__true__iff__false :
  ∀ (b : Original_LF__DOT__Basics_LF_Basics_bool), iff 
    (Corelib_Init_Logic_eq b Original_LF__DOT__Basics_LF_Basics_true → RocqFalse)
    (Corelib_Init_Logic_eq b Original_LF__DOT__Basics_LF_Basics_false)
