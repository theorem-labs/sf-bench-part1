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

-- List inductive type corresponding to Original.LF_DOT_Poly.LF.Poly.list
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

-- The nil constructor
def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

-- Equality in Prop (will become SProp in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- True in Prop (will become SProp in Rocq)
-- We need a custom True since Lean's built-in True can't be redefined
inductive MyTrue : Prop where
  | intro : MyTrue

-- forallb is Admitted in Original.v, so we axiomatize it
axiom Original_LF__DOT__Tactics_LF_Tactics_forallb : 
  {X : Type} → (X → Original_LF__DOT__Basics_LF_Basics_bool) → 
  Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Basics_LF_Basics_bool

-- test_forallb_4 is Admitted in Original.v, so we axiomatize it
-- It states: forallb (eqb 5) [] = true
axiom Original_LF__DOT__Tactics_LF_Tactics_test__forallb__4 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Tactics_LF_Tactics_forallb (Original_LF__DOT__Basics_LF_Basics_eqb (S (S (S (S (S _0))))))
      (Original_LF__DOT__Poly_LF_Poly_nil nat))
    Original_LF__DOT__Basics_LF_Basics_true
