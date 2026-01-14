-- Lean translation for test_remove_all3 and dependencies

-- We need to shadow/redefine True with a custom inductive
-- to get consistent export. We use a namespace trick.
namespace Exports
inductive True : Prop where
  | intro : True
end Exports

-- Equality in Prop (so it becomes SProp when imported)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality for Prop arguments
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

-- remove_all is admitted (axiom) in the original Rocq code
axiom Original_LF__DOT__Lists_LF_Lists_NatList_remove__all : nat → Original_LF__DOT__Lists_LF_Lists_NatList_bag → Original_LF__DOT__Lists_LF_Lists_NatList_bag

-- test_remove_all3 is admitted (axiom) in the original Rocq code
-- count 4 (remove_all 5 [2;1;4;5;1;4]) = 2
axiom Original_LF__DOT__Lists_LF_Lists_NatList_test__remove__all3 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_count 
       (S (S (S (S _0))))  -- 4
       (Original_LF__DOT__Lists_LF_Lists_NatList_remove__all 
          (S (S (S (S (S _0)))))  -- 5
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S _0))  -- 2
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)  -- 1
                (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S _0))))  -- 4
                   (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S (S _0)))))  -- 5
                      (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)  -- 1
                         (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S _0))))  -- 4
                            Original_LF__DOT__Lists_LF_Lists_NatList_nil))))))))
    (S (S _0))  -- 2
