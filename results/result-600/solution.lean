-- True in Prop (becomes SProp in Rocq)
inductive PTrue : Prop where
  | intro : PTrue

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Equality in Prop (so it becomes SProp when imported)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality for Prop arguments (also becomes SProp)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- natlist type (custom list of nats)
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natlist : Type where
  | nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist

-- natlist constructors
def Original_LF__DOT__Lists_LF_Lists_NatList_nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil

def Original_LF__DOT__Lists_LF_Lists_NatList_cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons

-- tail function
def Original_LF__DOT__Lists_LF_Lists_NatList_tl (l : Original_LF__DOT__Lists_LF_Lists_NatList_natlist) : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  match l with
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil => Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons _ t => t

-- test_tl theorem: tl [1;2;3] = [2;3]
-- In the original: Example test_tl: tl [1;2;3] = [2;3]. Admitted.
-- This is provable by reflexivity but we use axiom since original is Admitted
axiom Original_LF__DOT__Lists_LF_Lists_NatList_test__tl :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_tl
       (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S _0))
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S _0))) Original_LF__DOT__Lists_LF_Lists_NatList_nil))))
    (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S _0))
       (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S _0))) Original_LF__DOT__Lists_LF_Lists_NatList_nil))
