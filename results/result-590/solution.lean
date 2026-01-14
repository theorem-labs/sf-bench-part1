-- Equality in Prop (which imports as SProp in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- True as an alias for Lean's True (will be exported to SProp)
def MyTrue : Prop := _root_.True

-- NatList: list of natural numbers
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natlist : Type where
  | nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist

-- Constructors for natlist
def Original_LF__DOT__Lists_LF_Lists_NatList_nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil

def Original_LF__DOT__Lists_LF_Lists_NatList_cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons

-- Head function with default value
def Original_LF__DOT__Lists_LF_Lists_NatList_hd (default : nat) (l : Original_LF__DOT__Lists_LF_Lists_NatList_natlist) : nat :=
  match l with
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil => default
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h _ => h

-- natoption: an option type for nat
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natoption : Type where
  | Some : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natoption
  | None : Original_LF__DOT__Lists_LF_Lists_NatList_natoption

-- option_elim: extract value from natoption with default
def Original_LF__DOT__Lists_LF_Lists_NatList_option__elim (d : nat) (o : Original_LF__DOT__Lists_LF_Lists_NatList_natoption) : nat :=
  match o with
  | Original_LF__DOT__Lists_LF_Lists_NatList_natoption.Some n => n
  | Original_LF__DOT__Lists_LF_Lists_NatList_natoption.None => d

-- hd_error is admitted in the original, so we translate it as an axiom
axiom Original_LF__DOT__Lists_LF_Lists_NatList_hd__error : Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natoption

-- option_elim_hd is admitted in the original, so we translate it as an axiom
-- Theorem: forall l default, hd default l = option_elim default (hd_error l)
axiom Original_LF__DOT__Lists_LF_Lists_NatList_option__elim__hd : 
  ∀ (l : Original_LF__DOT__Lists_LF_Lists_NatList_natlist) (default : nat),
    Corelib_Init_Logic_eq 
      (Original_LF__DOT__Lists_LF_Lists_NatList_hd default l)
      (Original_LF__DOT__Lists_LF_Lists_NatList_option__elim default (Original_LF__DOT__Lists_LF_Lists_NatList_hd__error l))
