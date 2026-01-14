-- True in Prop
inductive PTrue : Prop where
  | intro : PTrue

-- Equality in Prop (so it becomes SProp when imported)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality specialized to Prop
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

-- app function (defined, not axiomatized)
def Original_LF__DOT__Lists_LF_Lists_NatList_app : Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil, l2 => l2
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h t, l2 => Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h (Original_LF__DOT__Lists_LF_Lists_NatList_app t l2)

-- nonzeros function - axiomatized since it's Admitted in the original
axiom Original_LF__DOT__Lists_LF_Lists_NatList_nonzeros : Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist

-- nonzeros_app theorem - axiomatized since it's Admitted in the original
axiom Original_LF__DOT__Lists_LF_Lists_NatList_nonzeros__app : ∀ (l1 l2 : Original_LF__DOT__Lists_LF_Lists_NatList_natlist),
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__Lists_LF_Lists_NatList_nonzeros (Original_LF__DOT__Lists_LF_Lists_NatList_app l1 l2))
    (Original_LF__DOT__Lists_LF_Lists_NatList_app 
      (Original_LF__DOT__Lists_LF_Lists_NatList_nonzeros l1) 
      (Original_LF__DOT__Lists_LF_Lists_NatList_nonzeros l2))
