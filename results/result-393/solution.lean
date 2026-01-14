-- Lean translation of Rocq definitions for eqblist_refl

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

-- Bool type (dependency)
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

-- true constructor
def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

-- natlist type (custom list of nats)
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natlist : Type where
  | nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist

-- Equality in Prop for Type (so it becomes SProp when imported)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality in Prop for Prop (so it becomes SProp when imported)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- True in Prop - we use Lean's builtin True
-- PTrue is an alias for the builtin True
abbrev PTrue : Prop := True

-- eqblist is an axiom (Admitted in original)
axiom Original_LF__DOT__Lists_LF_Lists_NatList_eqblist : Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Basics_LF_Basics_bool

-- eqblist_refl theorem (Admitted in original)
-- forall l : natlist, true = eqblist l l
axiom Original_LF__DOT__Lists_LF_Lists_NatList_eqblist__refl :
  ∀ (l : Original_LF__DOT__Lists_LF_Lists_NatList_natlist),
    Corelib_Init_Logic_eq Original_LF__DOT__Basics_LF_Basics_true (Original_LF__DOT__Lists_LF_Lists_NatList_eqblist l l)
