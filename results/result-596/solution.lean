-- Equality in Prop (which imports as SProp in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality for Prop (the first argument is a Prop)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- True as an alias for Lean's True (will be exported to SProp)
def MyTrue : Prop := _root_.True

-- NatList: list of natural numbers
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natlist : Type where
  | nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist

-- Constructors for natlist
def Original_LF__DOT__Lists_LF_Lists_NatList_nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil

def Original_LF__DOT__Lists_LF_Lists_NatList_cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons

-- Head function with default value
def Original_LF__DOT__Lists_LF_Lists_NatList_hd (default : nat) (l : Original_LF__DOT__Lists_LF_Lists_NatList_natlist) : nat :=
  match l with
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil => default
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h _ => h

-- The test_hd1 axiom: hd 0 [1;2;3] = 1
-- [1;2;3] = cons 1 (cons 2 (cons 3 nil))
-- hd 0 [1;2;3] = 1
-- So we need: hd 0 (cons (S 0) (cons (S (S 0)) (cons (S (S (S 0))) nil))) = S 0
axiom Original_LF__DOT__Lists_LF_Lists_NatList_test__hd1 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_hd _0
       (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S _0))
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S _0))) Original_LF__DOT__Lists_LF_Lists_NatList_nil))))
    (S _0)
