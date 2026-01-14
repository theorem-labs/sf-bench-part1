-- Lean translation for natlist, nil, cons, and mylist

-- Define nat as an alias for Nat (to get controlled export names)
inductive nat : Type where
  | O : nat
  | S : nat → nat

-- Define natlist (list of nats)
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natlist : Type where
  | nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist

-- Aliases for nil and cons
def Original_LF__DOT__Lists_LF_Lists_NatList_nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil

def Original_LF__DOT__Lists_LF_Lists_NatList_cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons

-- mylist = cons 1 (cons 2 (cons 3 nil)) = [1, 2, 3]
-- Define directly with nat.S to avoid intermediate definitions
def Original_LF__DOT__Lists_LF_Lists_NatList_mylist : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S nat.O)
    (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S (nat.S nat.O))
      (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S (nat.S (nat.S nat.O)))
        Original_LF__DOT__Lists_LF_Lists_NatList_nil))
