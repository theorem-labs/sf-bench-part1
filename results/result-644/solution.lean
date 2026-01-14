-- Lean translation for natlist, oddmembers and test_oddmembers

-- Define nat
inductive nat : Type where
  | O : nat
  | S : nat → nat

-- Alias for 0
def _0 : nat := nat.O

-- Alias for S
def S : nat → nat := nat.S

-- Define natlist (list of nats)
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natlist : Type where
  | nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist

-- Nil constructor
def Original_LF__DOT__Lists_LF_Lists_NatList_nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil

-- Cons constructor  
def Original_LF__DOT__Lists_LF_Lists_NatList_cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons

-- Equality in Prop (will be imported as SProp)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Export Lean's built-in True
-- Use #check True to verify it exists

-- oddmembers is admitted (axiom)
axiom Original_LF__DOT__Lists_LF_Lists_NatList_oddmembers : Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist

-- test_oddmembers is also admitted (axiom)
-- oddmembers [0;1;0;2;3;0;0] = [1;3]
axiom Original_LF__DOT__Lists_LF_Lists_NatList_test__oddmembers : 
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_oddmembers
       (Original_LF__DOT__Lists_LF_Lists_NatList_cons _0
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons _0
                (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S _0))
                   (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S _0)))
                      (Original_LF__DOT__Lists_LF_Lists_NatList_cons _0
                         (Original_LF__DOT__Lists_LF_Lists_NatList_cons _0 Original_LF__DOT__Lists_LF_Lists_NatList_nil))))))))
    (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)
       (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S _0))) Original_LF__DOT__Lists_LF_Lists_NatList_nil))
