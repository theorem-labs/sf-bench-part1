

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

-- mylist3 = [1;2;3] = cons 1 (cons 2 (cons 3 nil))
def Original_LF__DOT__Lists_LF_Lists_NatList_mylist3 : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S nat.O)
    (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S (nat.S nat.O))
      (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S (nat.S (nat.S nat.O)))
        Original_LF__DOT__Lists_LF_Lists_NatList_nil))

-- nonzeros function - axiomatized since it's Admitted in the original
axiom Original_LF__DOT__Lists_LF_Lists_NatList_nonzeros : Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist

-- test_nonzeros axiom
axiom Original_LF__DOT__Lists_LF_Lists_NatList_test__nonzeros : 
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_nonzeros
       (Original_LF__DOT__Lists_LF_Lists_NatList_cons _0
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons _0
                (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S _0))
                   (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S _0)))
                      (Original_LF__DOT__Lists_LF_Lists_NatList_cons _0
                         (Original_LF__DOT__Lists_LF_Lists_NatList_cons _0 Original_LF__DOT__Lists_LF_Lists_NatList_nil))))))))
    (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)
       (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S _0))
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S _0))) Original_LF__DOT__Lists_LF_Lists_NatList_nil)))
