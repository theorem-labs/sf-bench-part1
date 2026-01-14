-- True in Prop (will become SProp in Rocq)
-- We define our own True type that will be exported
inductive PTrue : Prop where
  | intro : PTrue

def PTrue_intro : PTrue := PTrue.intro

-- Equality in Prop (will become SProp in Rocq)
-- This mirrors the standard Eq but in Prop
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl a

-- Equality for Prop types (will become SProp equality in Rocq)
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

-- Nat.add
def Nat_add : nat → nat → nat
  | nat.O, m => m
  | nat.S n', m => nat.S (Nat_add n' m)

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

-- The zero_nbeq_plus_1 theorem (admitted in Original.v, so axiom here)
-- Statement: forall n, (0 =? (n + 1)) = false
axiom Original_LF__DOT__Basics_LF_Basics_zero__nbeq__plus__1 :
  ∀ (x : nat), Corelib_Init_Logic_eq
    (Original_LF__DOT__Basics_LF_Basics_eqb _0 (Nat_add x (S _0)))
    Original_LF__DOT__Basics_LF_Basics_false
