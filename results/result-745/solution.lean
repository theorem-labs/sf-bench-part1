-- Lean 4 translation of Rocq definitions

-- True in Prop
inductive PTrue : Prop where
  | intro : PTrue

-- Alias for True (so the checker can find Imported.True)
-- Using a different name since True is a Lean keyword
def MyTrue : Prop := PTrue

-- Equality in Prop (so it becomes SProp when imported)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

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
def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool := 
  Original_LF__DOT__Basics_LF_Basics_bool.true
def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool := 
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- natlist type (custom list of nats)
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natlist : Type where
  | nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist

-- natlist constructors
def Original_LF__DOT__Lists_LF_Lists_NatList_nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil

def Original_LF__DOT__Lists_LF_Lists_NatList_cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons

-- bag is an alias for natlist
def Original_LF__DOT__Lists_LF_Lists_NatList_bag : Type := Original_LF__DOT__Lists_LF_Lists_NatList_natlist

-- included function - axiomatized since it's Admitted in the original
axiom Original_LF__DOT__Lists_LF_Lists_NatList_included : Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Basics_LF_Basics_bool

-- test_included2: included [1;2;2] [2;1;4;1] = false
-- [1;2;2] = cons 1 (cons 2 (cons 2 nil))
-- [2;1;4;1] = cons 2 (cons 1 (cons 4 (cons 1 nil)))
axiom Original_LF__DOT__Lists_LF_Lists_NatList_test__included2 : 
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_included
       (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S _0))
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S _0)) Original_LF__DOT__Lists_LF_Lists_NatList_nil)))
       (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S _0))
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S _0))))
                (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0) Original_LF__DOT__Lists_LF_Lists_NatList_nil)))))
    Original_LF__DOT__Basics_LF_Basics_false
