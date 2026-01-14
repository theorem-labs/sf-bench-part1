-- True in Prop (will become SProp when imported)
inductive PTrue : Prop where
  | intro : PTrue

-- Equality in Prop (so it becomes SProp when imported) - for Type
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality for Prop (Prop → Prop → Prop, becomes SProp → SProp → SProp when imported)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

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

-- countoddmembers function - axiomatized since it's Admitted in the original
axiom Original_LF__DOT__Lists_LF_Lists_NatList_countoddmembers : Original_LF__DOT__Lists_LF_Lists_NatList_natlist → nat

-- test_countoddmembers3 axiom: countoddmembers nil = 0
axiom Original_LF__DOT__Lists_LF_Lists_NatList_test__countoddmembers3 : 
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_countoddmembers Original_LF__DOT__Lists_LF_Lists_NatList_nil)
    _0
