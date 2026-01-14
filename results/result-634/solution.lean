-- Lean translation for natlist, alternate, and test_alternate1
set_option autoImplicit false

-- Equality in Prop (will be exported to SProp)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- natlist (list of nats)
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natlist : Type where
  | nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist

-- nil and cons constructors
def Original_LF__DOT__Lists_LF_Lists_NatList_nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil

def Original_LF__DOT__Lists_LF_Lists_NatList_cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons

-- alternate is an axiom (admitted in Original.v)
axiom Original_LF__DOT__Lists_LF_Lists_NatList_alternate : 
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist → 
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist → 
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist

-- test_alternate1 is an axiom (admitted in Original.v)
-- alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6]
axiom Original_LF__DOT__Lists_LF_Lists_NatList_test__alternate1 : 
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_alternate
       (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S _0))
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S _0))) Original_LF__DOT__Lists_LF_Lists_NatList_nil)))
       (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S _0))))
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S (S _0)))))
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S (S (S _0)))))) Original_LF__DOT__Lists_LF_Lists_NatList_nil))))
    (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)
       (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S _0))))
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S _0))
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S (S _0)))))
                (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S _0)))
                   (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S (S (S _0)))))) Original_LF__DOT__Lists_LF_Lists_NatList_nil))))))
