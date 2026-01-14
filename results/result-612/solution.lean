-- Lean 4 translation for repeat_plus and its dependencies

set_option autoImplicit false

-- Define nat as an inductive type to match Rocq's nat  
inductive nat : Type where
  | O : nat
  | S : nat -> nat

-- Define Nat_add to match Rocq's Nat.add
def Nat_add : nat -> nat -> nat
  | nat.O, m => m
  | nat.S p, m => nat.S (Nat_add p m)

-- True: use a namespace that we can manually fix in the .out file
namespace X
inductive True : Prop where
  | intro : True
end X

-- Equality (in Prop to match Rocq) - specialized to Type
inductive Corelib_Init_Logic_eq {A : Type} (a : A) : A -> Prop where
  | refl : Corelib_Init_Logic_eq a a

-- Equality specialized to Prop
inductive Corelib_Init_Logic_eq_Prop {A : Prop} (a : A) : A -> Prop where
  | refl : Corelib_Init_Logic_eq_Prop a a

-- natlist (list of nats)
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natlist : Type where
  | nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | cons : nat -> Original_LF__DOT__Lists_LF_Lists_NatList_natlist -> Original_LF__DOT__Lists_LF_Lists_NatList_natlist

-- nil and cons aliases
def Original_LF__DOT__Lists_LF_Lists_NatList_nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil

def Original_LF__DOT__Lists_LF_Lists_NatList_cons : nat -> Original_LF__DOT__Lists_LF_Lists_NatList_natlist -> Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons

-- app function
def Original_LF__DOT__Lists_LF_Lists_NatList_app : Original_LF__DOT__Lists_LF_Lists_NatList_natlist -> Original_LF__DOT__Lists_LF_Lists_NatList_natlist -> Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil, l2 => l2
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h t, l2 => 
      Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h (Original_LF__DOT__Lists_LF_Lists_NatList_app t l2)

-- repeat function: repeat n count produces a list of count copies of n
def Original_LF__DOT__Lists_LF_Lists_NatList_repeat : nat -> nat -> Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | _, nat.O => Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil
  | n, nat.S count' => Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons n (Original_LF__DOT__Lists_LF_Lists_NatList_repeat n count')

-- repeat_plus theorem: repeat n c1 ++ repeat n c2 = repeat n (c1 + c2)
-- This is Admitted in Original.v, so we declare it as an axiom
axiom Original_LF__DOT__Lists_LF_Lists_NatList_repeat__plus : 
  forall (c1 c2 n : nat), 
    Corelib_Init_Logic_eq 
      (Original_LF__DOT__Lists_LF_Lists_NatList_app 
        (Original_LF__DOT__Lists_LF_Lists_NatList_repeat n c1) 
        (Original_LF__DOT__Lists_LF_Lists_NatList_repeat n c2))
      (Original_LF__DOT__Lists_LF_Lists_NatList_repeat n (Nat_add c1 c2))
