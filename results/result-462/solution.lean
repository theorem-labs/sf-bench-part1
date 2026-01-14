-- Lean translation for the remove_does_not_increase_count theorem and dependencies

-- Define nat
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O

-- Define bool (matching LF.Basics.bool)
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- Define leb (less or equal for booleans)
def Original_LF__DOT__Basics_LF_Basics_leb : nat → nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O, _ => Original_LF__DOT__Basics_LF_Basics_bool.true
  | nat.S _, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S n', nat.S m' => Original_LF__DOT__Basics_LF_Basics_leb n' m'

-- Define natlist (list of nats)
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natlist : Type where
  | nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist

-- bag is just an alias for natlist
def Original_LF__DOT__Lists_LF_Lists_NatList_bag : Type := Original_LF__DOT__Lists_LF_Lists_NatList_natlist

-- Equality in Prop (will become SProp in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- True in Prop (use MyTrue to avoid conflict with Lean's built-in True)
inductive MyTrue : Prop where
  | intro : MyTrue

-- count is admitted in the original Rocq code, so axiom here
axiom Original_LF__DOT__Lists_LF_Lists_NatList_count : nat → Original_LF__DOT__Lists_LF_Lists_NatList_bag → nat

-- remove_one is admitted in the original Rocq code, so axiom here
axiom Original_LF__DOT__Lists_LF_Lists_NatList_remove__one : nat → Original_LF__DOT__Lists_LF_Lists_NatList_bag → Original_LF__DOT__Lists_LF_Lists_NatList_bag

-- The theorem remove_does_not_increase_count (admitted in Original.v)
axiom Original_LF__DOT__Lists_LF_Lists_NatList_remove__does__not__increase__count :
  ∀ (x : Original_LF__DOT__Lists_LF_Lists_NatList_bag),
    Corelib_Init_Logic_eq
      (Original_LF__DOT__Basics_LF_Basics_leb
        (Original_LF__DOT__Lists_LF_Lists_NatList_count _0 (Original_LF__DOT__Lists_LF_Lists_NatList_remove__one _0 x))
        (Original_LF__DOT__Lists_LF_Lists_NatList_count _0 x))
      Original_LF__DOT__Basics_LF_Basics_true
