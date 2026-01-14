-- True in Prop
def True_def : Prop := _root_.True

-- Equality in Prop (exported as SProp) - for Type arguments
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality in Prop (exported as SProp) - for Prop arguments
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Arithmetic expressions
inductive Original_LF__DOT__Imp_LF_Imp_AExp_aexp : Type where
  | ANum : nat → Original_LF__DOT__Imp_LF_Imp_AExp_aexp
  | APlus : Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp
  | AMinus : Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp
  | AMult : Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp

def Original_LF__DOT__Imp_LF_Imp_AExp_ANum := Original_LF__DOT__Imp_LF_Imp_AExp_aexp.ANum
def Original_LF__DOT__Imp_LF_Imp_AExp_APlus := Original_LF__DOT__Imp_LF_Imp_AExp_aexp.APlus

-- Optimize 0plus: remove additions with 0 on the left
-- This matches the original Rocq definition exactly:
-- match a with
-- | ANum n => ANum n
-- | APlus (ANum 0) e2 => optimize_0plus e2
-- | APlus e1 e2 => APlus (optimize_0plus e1) (optimize_0plus e2)
-- | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
-- | AMult e1 e2 => AMult (optimize_0plus e1) (optimize_0plus e2)
def Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus : Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp
  | Original_LF__DOT__Imp_LF_Imp_AExp_aexp.ANum n => Original_LF__DOT__Imp_LF_Imp_AExp_aexp.ANum n
  | Original_LF__DOT__Imp_LF_Imp_AExp_aexp.APlus (Original_LF__DOT__Imp_LF_Imp_AExp_aexp.ANum nat.O) e2 =>
      Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus e2
  | Original_LF__DOT__Imp_LF_Imp_AExp_aexp.APlus e1 e2 =>
      Original_LF__DOT__Imp_LF_Imp_AExp_aexp.APlus
        (Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus e1)
        (Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus e2)
  | Original_LF__DOT__Imp_LF_Imp_AExp_aexp.AMinus e1 e2 =>
      Original_LF__DOT__Imp_LF_Imp_AExp_aexp.AMinus
        (Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus e1)
        (Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus e2)
  | Original_LF__DOT__Imp_LF_Imp_AExp_aexp.AMult e1 e2 =>
      Original_LF__DOT__Imp_LF_Imp_AExp_aexp.AMult
        (Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus e1)
        (Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus e2)

-- test_optimize_0plus: 
-- optimize_0plus (APlus (ANum 2) (APlus (ANum 0) (APlus (ANum 0) (ANum 1)))) = APlus (ANum 2) (ANum 1)
-- This is an admitted theorem in the original, so we use an axiom
axiom Original_LF__DOT__Imp_LF_Imp_AExp_test__optimize__0plus :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus
       (Original_LF__DOT__Imp_LF_Imp_AExp_APlus (Original_LF__DOT__Imp_LF_Imp_AExp_ANum (S (S _0)))
          (Original_LF__DOT__Imp_LF_Imp_AExp_APlus (Original_LF__DOT__Imp_LF_Imp_AExp_ANum _0)
             (Original_LF__DOT__Imp_LF_Imp_AExp_APlus (Original_LF__DOT__Imp_LF_Imp_AExp_ANum _0) (Original_LF__DOT__Imp_LF_Imp_AExp_ANum (S _0))))))
    (Original_LF__DOT__Imp_LF_Imp_AExp_APlus (Original_LF__DOT__Imp_LF_Imp_AExp_ANum (S (S _0)))
       (Original_LF__DOT__Imp_LF_Imp_AExp_ANum (S _0)))
