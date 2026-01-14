-- True in Prop (will become SProp in Rocq)
abbrev MyTrue : Prop := _root_.True

-- Equality in Prop (will become SProp in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl a

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

-- even function
def Original_LF__DOT__Basics_LF_Basics_even : nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O => Original_LF__DOT__Basics_LF_Basics_bool.true
  | nat.S nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S (nat.S n') => Original_LF__DOT__Basics_LF_Basics_even n'

-- List type (matching LF.Poly.list)
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

def Original_LF__DOT__Poly_LF_Poly_cons (X : Type) : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons

-- existsb function (admitted in Original.v, so axiom here)
axiom Original_LF__DOT__Tactics_LF_Tactics_existsb : {X : Type} → (X → Original_LF__DOT__Basics_LF_Basics_bool) → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Basics_LF_Basics_bool

-- test_existsb_4 : existsb even [] = false (admitted in Original.v)
axiom Original_LF__DOT__Tactics_LF_Tactics_test__existsb__4 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Tactics_LF_Tactics_existsb Original_LF__DOT__Basics_LF_Basics_even (Original_LF__DOT__Poly_LF_Poly_nil nat))
    Original_LF__DOT__Basics_LF_Basics_false
