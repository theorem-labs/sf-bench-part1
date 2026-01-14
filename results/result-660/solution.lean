-- Lean translation for test_rev1

-- Natural numbers 
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Equality in Prop for Type arguments (gets exported as SProp)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl : (a : A) → Corelib_Init_Logic_eq a a

-- Equality in Prop for Prop arguments (also SProp)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl : (a : A) → Corelib_Init_Logic_eq_Prop a a

-- True (renamed to avoid clash with Lean's built-in)
inductive TrueP : Prop where
  | intro : TrueP

-- natlist (list of nats)
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natlist : Type where
  | nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist

-- nil and cons aliases
def Original_LF__DOT__Lists_LF_Lists_NatList_nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil

def Original_LF__DOT__Lists_LF_Lists_NatList_cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons

-- app function (list append)
def Original_LF__DOT__Lists_LF_Lists_NatList_app : Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil, l2 => l2
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h t, l2 => 
      Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h (Original_LF__DOT__Lists_LF_Lists_NatList_app t l2)

-- rev function (list reverse)
def Original_LF__DOT__Lists_LF_Lists_NatList_rev : Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil => Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h t => 
      Original_LF__DOT__Lists_LF_Lists_NatList_app 
        (Original_LF__DOT__Lists_LF_Lists_NatList_rev t) 
        (Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil)

-- test_rev1: rev [1;2;3] = [3;2;1]
axiom Original_LF__DOT__Lists_LF_Lists_NatList_test__rev1 : 
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_rev
       (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S _0))
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S _0))) Original_LF__DOT__Lists_LF_Lists_NatList_nil))))
    (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S _0)))
       (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S _0))
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0) Original_LF__DOT__Lists_LF_Lists_NatList_nil)))
