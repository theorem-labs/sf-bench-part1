-- True in Prop (will become SProp in Rocq)
abbrev MyTrue : Prop := _root_.True

-- Equality in Prop (will become SProp in Rocq)
-- This mirrors the standard Eq but in Prop
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl a

-- Equality for Prop (which becomes SProp in Rocq)
-- This is a separate inductive for equality over Prop values
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

-- eqb function (equality test for nat)
def Original_LF__DOT__Basics_LF_Basics_eqb : nat → nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.true
  | nat.O, nat.S _ => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S _, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S n', nat.S m' => Original_LF__DOT__Basics_LF_Basics_eqb n' m'

-- The id type (wraps a natural number)
inductive Original_LF__DOT__Lists_LF_Lists_id : Type where
  | Id : nat → Original_LF__DOT__Lists_LF_Lists_id

-- The eqb_id function (equality test for id)
def Original_LF__DOT__Lists_LF_Lists_eqb__id (x1 x2 : Original_LF__DOT__Lists_LF_Lists_id) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match x1, x2 with
  | Original_LF__DOT__Lists_LF_Lists_id.Id n1, Original_LF__DOT__Lists_LF_Lists_id.Id n2 =>
    Original_LF__DOT__Basics_LF_Basics_eqb n1 n2

-- The eqb_id_refl theorem (admitted in Original.v, so axiom here)
axiom Original_LF__DOT__Lists_LF_Lists_eqb__id__refl :
  ∀ (x : Original_LF__DOT__Lists_LF_Lists_id),
    Corelib_Init_Logic_eq
      (Original_LF__DOT__Lists_LF_Lists_eqb__id x x)
      Original_LF__DOT__Basics_LF_Basics_true
