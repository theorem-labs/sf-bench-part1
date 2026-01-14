-- Lean translation for test_remove_one2 and dependencies

set_option allowUnsafeReducibility true

-- We need to export as "True" but can't use that name directly in Lean
-- So we use PTrue and will patch the .out file afterwards
inductive PTrue : Prop where
  | intro : PTrue

def PTrue_intro : PTrue := PTrue.intro

-- Equality in Prop (so it becomes SProp when imported)
-- Version for Type
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Version for Prop (needed by checker)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- natlist type (custom list of nats)
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natlist : Type where
  | nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist

-- natlist constructors
def Original_LF__DOT__Lists_LF_Lists_NatList_nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil

def Original_LF__DOT__Lists_LF_Lists_NatList_cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons

-- bag is a type alias for natlist
def Original_LF__DOT__Lists_LF_Lists_NatList_bag : Type := Original_LF__DOT__Lists_LF_Lists_NatList_natlist

-- count is admitted (axiom) in the original Rocq code
axiom Original_LF__DOT__Lists_LF_Lists_NatList_count : nat → Original_LF__DOT__Lists_LF_Lists_NatList_bag → nat

-- remove_one is admitted (axiom) in the original Rocq code
axiom Original_LF__DOT__Lists_LF_Lists_NatList_remove__one : nat → Original_LF__DOT__Lists_LF_Lists_NatList_bag → Original_LF__DOT__Lists_LF_Lists_NatList_bag

-- test_remove_one2: count 5 (remove_one 5 [2;1;4;1]) = 0
-- The list is [2;1;4;1] which has no 5s, so removing one 5 still gives a list with 0 fives
axiom Original_LF__DOT__Lists_LF_Lists_NatList_test__remove__one2 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_count 
       (S (S (S (S (S _0)))))  -- 5
       (Original_LF__DOT__Lists_LF_Lists_NatList_remove__one 
          (S (S (S (S (S _0)))))  -- 5
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S _0))  -- 2
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)  -- 1
                (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S _0))))  -- 4
                   (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)  -- 1
                      Original_LF__DOT__Lists_LF_Lists_NatList_nil))))))
    _0  -- 0
