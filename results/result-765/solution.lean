-- Lean translation for count_member_nonzero theorem and dependencies

-- Define nat
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

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

-- cons constructor as a definition
def Original_LF__DOT__Lists_LF_Lists_NatList_cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons

-- bag is just an alias for natlist
def Original_LF__DOT__Lists_LF_Lists_NatList_bag : Type := Original_LF__DOT__Lists_LF_Lists_NatList_natlist

-- Equality in Prop (will become SProp in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality for Props in Prop (SProp arguments)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- Custom True in Prop (use PTrue to avoid conflict with Lean's built-in True)
inductive PTrue : Prop where
  | intro : PTrue

-- count is admitted in the original Rocq code, so axiom here
axiom Original_LF__DOT__Lists_LF_Lists_NatList_count : nat → Original_LF__DOT__Lists_LF_Lists_NatList_bag → nat

-- count_member_nonzero: forall (s : bag), 1 <=? (count 1 (1 :: s)) = true
-- Admitted in Original.v, so axiom here
axiom Original_LF__DOT__Lists_LF_Lists_NatList_count__member__nonzero :
  ∀ (x : Original_LF__DOT__Lists_LF_Lists_NatList_natlist),
    Corelib_Init_Logic_eq
      (Original_LF__DOT__Basics_LF_Basics_leb (S _0)
         (Original_LF__DOT__Lists_LF_Lists_NatList_count (S _0) (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0) x)))
      Original_LF__DOT__Basics_LF_Basics_true
