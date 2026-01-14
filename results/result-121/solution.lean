-- Lean translation for nth_bad and dependencies

-- Define nat to match Rocq's nat
inductive nat : Type where
  | O : nat
  | S : nat → nat

-- Define natlist to match Rocq's Original.LF_DOT_Lists.LF.Lists.NatList.natlist
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natlist : Type where
  | nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist

-- Define nth_bad
def Original_LF__DOT__Lists_LF_Lists_NatList_nth__bad 
    (l : Original_LF__DOT__Lists_LF_Lists_NatList_natlist) (n : nat) : nat :=
  match l with
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil => 
      nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S 
      (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S 
      (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S 
      (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S 
      (nat.S (nat.S nat.O)))))))))))))))))))))))))))))))))))))))))  -- 42
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons a l' =>
      match n with
      | nat.O => a
      | nat.S n' => Original_LF__DOT__Lists_LF_Lists_NatList_nth__bad l' n'
