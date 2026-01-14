-- Lean translation for natlist, app, rev, length and rev_length theorem

set_option autoImplicit false

-- Define nat 
inductive nat : Type where
  | O : nat
  | S : nat → nat

-- S function alias
def S : nat → nat := nat.S

-- Define natlist (list of nats)
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natlist : Type where
  | nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist

-- nil alias
def Original_LF__DOT__Lists_LF_Lists_NatList_nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil

-- cons alias
def Original_LF__DOT__Lists_LF_Lists_NatList_cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons

-- Define length function
def Original_LF__DOT__Lists_LF_Lists_NatList_length : Original_LF__DOT__Lists_LF_Lists_NatList_natlist → nat
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil => nat.O
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons _ t => nat.S (Original_LF__DOT__Lists_LF_Lists_NatList_length t)

-- Define app function
def Original_LF__DOT__Lists_LF_Lists_NatList_app : Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil, l2 => l2
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h t, l2 => 
      Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h (Original_LF__DOT__Lists_LF_Lists_NatList_app t l2)

-- Define rev function (list reverse)
def Original_LF__DOT__Lists_LF_Lists_NatList_rev : Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil => Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h t => 
      Original_LF__DOT__Lists_LF_Lists_NatList_app 
        (Original_LF__DOT__Lists_LF_Lists_NatList_rev t) 
        (Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil)

-- Equality type in Prop (will become SProp in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl : ∀ (a : A), Corelib_Init_Logic_eq a a

-- True in Prop (custom definition for export)
inductive MyTrue : Prop where
  | intro : MyTrue

-- The rev_length theorem as an axiom (since it's Admitted in Original.v)
axiom Original_LF__DOT__Lists_LF_Lists_NatList_rev__length : 
  ∀ (l : Original_LF__DOT__Lists_LF_Lists_NatList_natlist),
    @Corelib_Init_Logic_eq nat
      (Original_LF__DOT__Lists_LF_Lists_NatList_length (Original_LF__DOT__Lists_LF_Lists_NatList_rev l))
      (Original_LF__DOT__Lists_LF_Lists_NatList_length l)
