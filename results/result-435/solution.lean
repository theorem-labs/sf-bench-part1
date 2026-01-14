-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Natural number addition
def nat_add : nat → nat → nat
  | nat.O, m => m
  | nat.S n, m => nat.S (nat_add n m)

-- le as an inductive type matching Rocq's le
inductive le : nat → nat → Prop where
  | le_n (n : nat) : le n n
  | le_S (n m : nat) : le n m → le n (nat.S m)

-- ge as le n m (i.e., ge m n = le n m)
def ge (m n : nat) : Prop := le n m

-- Regular expression type (matching Original.LF_DOT_IndProp.LF.IndProp.reg_exp)
inductive Original_LF__DOT__IndProp_LF_IndProp_reg__exp (T : Type) : Type where
  | EmptySet : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | EmptyStr : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Char : T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | App : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Union : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Star : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T

-- pumping_constant function
def Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant {T : Type} (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : nat :=
  match re with
  | Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptySet => nat.S nat.O  -- 1
  | Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptyStr => nat.S nat.O  -- 1
  | Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Char _ => nat.S (nat.S nat.O)  -- 2
  | Original_LF__DOT__IndProp_LF_IndProp_reg__exp.App re1 re2 =>
      nat_add (Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant re1)
              (Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant re2)
  | Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Union re1 re2 =>
      nat_add (Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant re1)
              (Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant re2)
  | Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star r =>
      Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant r

-- pumping_constant_ge_1: pumping_constant is always >= 1
-- This is Admitted in the original, so we axiomatize it
axiom Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant__ge__1 :
  ∀ (T : Type) (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T),
    ge (Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant re) (S _0)
