-- Lean 4 translation for R_equiv_fR and all dependencies
set_option autoImplicit false

-- True (unit type in Prop)
-- Define an alias for Lean's True - this will export as True
abbrev RocqTrue : Prop := True

-- Define the intro constructor as a def
def RocqTrue_intro : RocqTrue := True.intro

-- iff (biconditional)
structure iff (A B : Prop) : Prop where
  mp : A → B
  mpr : B → A

-- Equality in Prop for Type
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality in Prop for Prop
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

-- The R relation from LF.IndProp
inductive Original_LF__DOT__IndProp_LF_IndProp_R : nat → nat → nat → Prop where
  | c1 : Original_LF__DOT__IndProp_LF_IndProp_R nat.O nat.O nat.O
  | c2 : ∀ (m n o : nat), Original_LF__DOT__IndProp_LF_IndProp_R m n o → Original_LF__DOT__IndProp_LF_IndProp_R (nat.S m) n (nat.S o)
  | c3 : ∀ (m n o : nat), Original_LF__DOT__IndProp_LF_IndProp_R m n o → Original_LF__DOT__IndProp_LF_IndProp_R m (nat.S n) (nat.S o)
  | c4 : ∀ (m n o : nat), Original_LF__DOT__IndProp_LF_IndProp_R (nat.S m) (nat.S n) (nat.S (nat.S o)) → Original_LF__DOT__IndProp_LF_IndProp_R m n o
  | c5 : ∀ (m n o : nat), Original_LF__DOT__IndProp_LF_IndProp_R m n o → Original_LF__DOT__IndProp_LF_IndProp_R n m o

-- fR is an admitted axiom in Original.v, so we translate it as an axiom
axiom Original_LF__DOT__IndProp_LF_IndProp_fR : nat → nat → nat

-- R_equiv_fR is an admitted theorem in Original.v, so we translate it as an axiom
axiom Original_LF__DOT__IndProp_LF_IndProp_R__equiv__fR :
  ∀ (m n o : nat), iff (Original_LF__DOT__IndProp_LF_IndProp_R m n o) (Corelib_Init_Logic_eq (Original_LF__DOT__IndProp_LF_IndProp_fR m n) o)
