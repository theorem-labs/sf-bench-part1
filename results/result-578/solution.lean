-- True in Prop (will become SProp in Rocq)
abbrev MyTrue : Prop := _root_.True

-- Equality in Prop (will become SProp in Rocq) - Type version
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl a

-- Equality in Prop (will become SProp in Rocq) - Prop version
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

-- sillyfun function
def Original_LF__DOT__Tactics_LF_Tactics_sillyfun (n : nat) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match Original_LF__DOT__Basics_LF_Basics_eqb n (nat.S (nat.S (nat.S nat.O))) with  -- n =? 3
  | .true => Original_LF__DOT__Basics_LF_Basics_bool.false
  | .false =>
    match Original_LF__DOT__Basics_LF_Basics_eqb n (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))) with  -- n =? 5
    | .true => Original_LF__DOT__Basics_LF_Basics_bool.false
    | .false => Original_LF__DOT__Basics_LF_Basics_bool.false

-- sillyfun_false theorem (admitted in Original.v, so axiom here)
axiom Original_LF__DOT__Tactics_LF_Tactics_sillyfun__false :
  ∀ (n : nat), Corelib_Init_Logic_eq
    (Original_LF__DOT__Tactics_LF_Tactics_sillyfun n)
    Original_LF__DOT__Basics_LF_Basics_false
