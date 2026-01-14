-- Translation of nat, natprod, and fst' from Rocq to Lean

-- Define nat to match Rocq's nat
inductive nat : Type where
  | O : nat
  | S : nat → nat

-- Define natprod to match Rocq's LF_DOT_Lists.LF.Lists.NatList.natprod
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natprod : Type where
  | pair : nat → nat → Original_LF__DOT__Lists_LF_Lists_NatList_natprod

-- Define fst' to match Rocq's LF_DOT_Lists.LF.Lists.NatList.fst'
def Original_LF__DOT__Lists_LF_Lists_NatList_fst' (p : Original_LF__DOT__Lists_LF_Lists_NatList_natprod) : nat :=
  match p with
  | Original_LF__DOT__Lists_LF_Lists_NatList_natprod.pair x _ => x
