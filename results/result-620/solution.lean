-- Lean translation for test_app2

-- Natural numbers 
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Equality in Prop (which gets exported as SProp) - for Type arguments
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl : (a : A) → Corelib_Init_Logic_eq a a

-- Equality in Prop (for Prop arguments) - maps to SProp -> SProp -> SProp
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl : (a : A) → Corelib_Init_Logic_eq_Prop a a

-- True in SProp (named MyTrue to avoid conflict with Lean's True)
inductive MyTrue : Prop where
  | intro : MyTrue

def MyTrue_intro : MyTrue := MyTrue.intro

-- natlist (list of nats)
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natlist : Type where
  | nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist

-- nil and cons aliases
def Original_LF__DOT__Lists_LF_Lists_NatList_nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil

def Original_LF__DOT__Lists_LF_Lists_NatList_cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons

-- app function
def Original_LF__DOT__Lists_LF_Lists_NatList_app : Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil, l2 => l2
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h t, l2 => 
      Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h (Original_LF__DOT__Lists_LF_Lists_NatList_app t l2)

-- test_app2: nil ++ [4;5] = [4;5]
-- This is an Admitted theorem in the original, so we use axiom here
axiom Original_LF__DOT__Lists_LF_Lists_NatList_test__app2 : 
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_app
       Original_LF__DOT__Lists_LF_Lists_NatList_nil
       (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S _0))))
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S (S _0))))) Original_LF__DOT__Lists_LF_Lists_NatList_nil)))
    (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S _0))))
       (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S (S _0))))) Original_LF__DOT__Lists_LF_Lists_NatList_nil))
