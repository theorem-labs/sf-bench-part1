-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Natural number operations
def nat_add : nat → nat → nat
  | nat.O, m => m
  | nat.S n, m => nat.S (nat_add n m)

-- False proposition  
inductive Original_False : Prop where

-- True proposition - define our own inductive since we can't redefine True
inductive TrueProp : Prop where
  | I : TrueProp

def True_I : TrueProp := TrueProp.I

-- Equality in Prop (for Type arguments)
inductive eq' (A : Type) : A → A → Prop where
  | refl (a : A) : eq' A a a

def Corelib_Init_Logic_eq {A : Type} (x y : A) : Prop := eq' A x y

-- Equality in Prop (for Prop arguments)
inductive eq'_Prop (A : Prop) : A → A → Prop where
  | refl (a : A) : eq'_Prop A a a

def Corelib_Init_Logic_eq_Prop {A : Prop} (x y : A) : Prop := eq'_Prop A x y

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

-- pumping_constant_0_false: pumping_constant is never 0
-- This is Admitted in the original, so we axiomatize it
axiom Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant__0__false :
  ∀ (T : Type) (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T),
    Corelib_Init_Logic_eq (Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant re) _0 → Original_False
