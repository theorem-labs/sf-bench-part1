-- Lean translation for test_count2 and all dependencies

-- True in Prop (becomes SProp when imported)
inductive PTrue : Prop where
  | intro : PTrue

-- Equality in Prop (becomes SProp when imported)
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

-- bag is just a type alias for natlist
def Original_LF__DOT__Lists_LF_Lists_NatList_bag : Type := Original_LF__DOT__Lists_LF_Lists_NatList_natlist

-- count function - axiomatized since it's Admitted in the original
axiom Original_LF__DOT__Lists_LF_Lists_NatList_count : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → nat

-- test_count2 axiom: count 6 [1;2;3;1;4;1] = 0
-- 6 = S (S (S (S (S (S O))))) = S (S (S (iterate1 S 3 0)))
-- iterate1 S 3 0 = S (S (S O)) = 3
-- So 6 = S (S (S (S (S (S O)))))
axiom Original_LF__DOT__Lists_LF_Lists_NatList_test__count2 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_count
       (S (S (S (S (S (S _0))))))  -- 6
       (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)  -- 1
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S _0))  -- 2
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S _0)))  -- 3
                (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)  -- 1
                   (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S _0))))  -- 4
                      (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0) Original_LF__DOT__Lists_LF_Lists_NatList_nil)))))))  -- 1
    _0  -- 0
