-- Lean 4 translation for eqb_neq and all dependencies
set_option autoImplicit false

-- True (unit type in Prop) - renamed to avoid conflict
inductive RocqTrue : Prop where
  | intro : RocqTrue

-- False (empty type in Prop) - renamed to avoid conflict
inductive RocqFalse : Prop where

-- Logic.not (negation)
def Logic_not (P : Prop) : Prop := P → RocqFalse

-- iff (biconditional)
structure iff (A B : Prop) : Prop where
  mp : A → B
  mpr : B → A

-- Equality in Prop
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

-- Boolean type
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- eqb function (equality test for nat)
def Original_LF__DOT__Basics_LF_Basics_eqb : nat → nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.true
  | nat.O, nat.S _ => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S _, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S n', nat.S m' => Original_LF__DOT__Basics_LF_Basics_eqb n' m'

-- eqb_neq: x =? y = false <-> x <> y
-- This is Admitted in Original.v, so we use axiom
axiom Original_LF__DOT__Logic_LF_Logic_eqb__neq :
  ∀ (x y : nat), iff 
    (Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_eqb x y) Original_LF__DOT__Basics_LF_Basics_false)
    (Corelib_Init_Logic_eq x y → RocqFalse)
