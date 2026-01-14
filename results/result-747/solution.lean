-- Lean 4 translation of Rocq definitions for test_member2

-- Equality in Prop (becomes SProp when imported to Rocq)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- True in Prop
inductive PTrue : Prop where
  | intro : PTrue

-- Since we can't shadow True, let's use the Lean4 True directly
-- and ensure it exports correctly

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Bool type (from LF.Basics)
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

-- Explicit definitions for true and false
def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool := Original_LF__DOT__Basics_LF_Basics_bool.true
def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool := Original_LF__DOT__Basics_LF_Basics_bool.false

-- natlist type (custom list of nats)
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natlist : Type where
  | nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist

-- natlist constructors
def Original_LF__DOT__Lists_LF_Lists_NatList_nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil

def Original_LF__DOT__Lists_LF_Lists_NatList_cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons

-- bag is just an alias for natlist
def Original_LF__DOT__Lists_LF_Lists_NatList_bag : Type := Original_LF__DOT__Lists_LF_Lists_NatList_natlist

-- member function - axiomatized since it's Admitted in the original
axiom Original_LF__DOT__Lists_LF_Lists_NatList_member : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Basics_LF_Basics_bool

-- test_member2 axiom: member 2 [1;4;1] = false
axiom Original_LF__DOT__Lists_LF_Lists_NatList_test__member2 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_member (S (S _0))
       (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S _0))))
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0) Original_LF__DOT__Lists_LF_Lists_NatList_nil))))
    Original_LF__DOT__Basics_LF_Basics_false
