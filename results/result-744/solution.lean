-- Lean translation of Rocq definitions for test_included1

-- Natural numbers (using Mynat to avoid shadowing)
inductive Mynat : Type where
  | O : Mynat
  | S : Mynat → Mynat

def _0 : Mynat := Mynat.O
def S : Mynat → Mynat := Mynat.S

-- natlist type (custom list of nats)
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natlist : Type where
  | nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | cons : Mynat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist

-- natlist constructors
def Original_LF__DOT__Lists_LF_Lists_NatList_nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil

def Original_LF__DOT__Lists_LF_Lists_NatList_cons : Mynat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons

-- bag is just an alias for natlist
def Original_LF__DOT__Lists_LF_Lists_NatList_bag : Type := Original_LF__DOT__Lists_LF_Lists_NatList_natlist

-- Bool type
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

-- true constructor
def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

-- Equality in Prop (will become SProp when imported)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- True in Prop
inductive PTrue : Prop where
  | intro : PTrue

-- included function - axiomatized since it's Admitted in the original
axiom Original_LF__DOT__Lists_LF_Lists_NatList_included : Original_LF__DOT__Lists_LF_Lists_NatList_bag → Original_LF__DOT__Lists_LF_Lists_NatList_bag → Original_LF__DOT__Basics_LF_Basics_bool

-- test_included1: included [1;2] [2;1;4;1] = true (Admitted in original)
axiom Original_LF__DOT__Lists_LF_Lists_NatList_test__included1 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_included
       (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S _0)) Original_LF__DOT__Lists_LF_Lists_NatList_nil))
       (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S _0))
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S _0))))
                (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0) Original_LF__DOT__Lists_LF_Lists_NatList_nil)))))
    Original_LF__DOT__Basics_LF_Basics_true
