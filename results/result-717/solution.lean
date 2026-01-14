-- Lean translation for test_remove_one4 and dependencies

-- True in Prop
inductive PTrue : Prop where
  | intro : PTrue

-- Equality in Prop (so it becomes SProp when imported)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

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

-- test_remove_one4 is admitted (axiom) in the original Rocq code
-- count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1
axiom Original_LF__DOT__Lists_LF_Lists_NatList_test__remove__one4 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_count 
       (S (S (S (S (S _0)))))  -- 5
       (Original_LF__DOT__Lists_LF_Lists_NatList_remove__one 
          (S (S (S (S (S _0)))))  -- 5
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S _0))  -- 2
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)  -- 1
                (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S (S _0)))))  -- 5
                   (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S _0))))  -- 4
                      (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S (S _0)))))  -- 5
                         (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)  -- 1
                            (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S _0))))  -- 4
                               Original_LF__DOT__Lists_LF_Lists_NatList_nil)))))))))
    (S _0)  -- 1
