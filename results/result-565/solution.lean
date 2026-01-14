-- Custom True type - we can't use the name "True" since it's builtin
-- We'll export it and manually edit Imported.out if needed
inductive MyTrue : Prop where
  | intro : MyTrue

def MyTrue_intro : MyTrue := MyTrue.intro

-- Equality in Prop (will become SProp in Rocq)
-- For Type arguments
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl a

-- For Prop arguments (will become SProp -> SProp -> SProp in Rocq)
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

-- Boolean type (matching LF.Basics.bool)
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- leb function (less-than-or-equal test for nat)
def Original_LF__DOT__Basics_LF_Basics_leb : nat → nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O, _ => Original_LF__DOT__Basics_LF_Basics_bool.true
  | nat.S _, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S n', nat.S m' => Original_LF__DOT__Basics_LF_Basics_leb n' m'

-- leb_n_Sn: for all n, leb n (S n) = true
-- This is Admitted in Original.v, so we use sorry (axiom)
axiom Original_LF__DOT__Lists_LF_Lists_NatList_leb__n__Sn :
  ∀ (n : nat), Corelib_Init_Logic_eq
    (Original_LF__DOT__Basics_LF_Basics_leb n (S n))
    Original_LF__DOT__Basics_LF_Basics_true
