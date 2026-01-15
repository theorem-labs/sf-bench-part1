-- MyTrue as alias for Lean's True (Prop in Lean becomes SProp in Rocq)
def MyTrue : Prop := _root_.True
def True_intro : MyTrue := _root_.True.intro

-- Equality in Prop (exported as SProp)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality for Prop types (first argument is Prop, exported as SProp)
-- For SProp elements, any two are equal, so we just return True
def Corelib_Init_Logic_eq_Prop {A : Prop} (x y : A) : Prop := MyTrue

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

-- Boolean expressions
inductive Original_LF__DOT__Imp_LF_Imp_AExp_bexp : Type where
  | BTrue : Original_LF__DOT__Imp_LF_Imp_AExp_bexp
  | BFalse : Original_LF__DOT__Imp_LF_Imp_AExp_bexp
  | BEq : Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_bexp
  | BNeq : Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_bexp
  | BLe : Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_bexp
  | BGt : Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_bexp
  | BNot : Original_LF__DOT__Imp_LF_Imp_AExp_bexp → Original_LF__DOT__Imp_LF_Imp_AExp_bexp
  | BAnd : Original_LF__DOT__Imp_LF_Imp_AExp_bexp → Original_LF__DOT__Imp_LF_Imp_AExp_bexp → Original_LF__DOT__Imp_LF_Imp_AExp_bexp

def Original_LF__DOT__Imp_LF_Imp_AExp_BGt := Original_LF__DOT__Imp_LF_Imp_AExp_bexp.BGt
def Original_LF__DOT__Imp_LF_Imp_AExp_BNot := Original_LF__DOT__Imp_LF_Imp_AExp_bexp.BNot
def Original_LF__DOT__Imp_LF_Imp_AExp_BTrue := Original_LF__DOT__Imp_LF_Imp_AExp_bexp.BTrue
def Original_LF__DOT__Imp_LF_Imp_AExp_BLe := Original_LF__DOT__Imp_LF_Imp_AExp_bexp.BLe
def Original_LF__DOT__Imp_LF_Imp_AExp_BAnd := Original_LF__DOT__Imp_LF_Imp_AExp_bexp.BAnd

-- optimize_0plus_b is an axiom in the original (Admitted)
axiom Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b : Original_LF__DOT__Imp_LF_Imp_AExp_bexp → Original_LF__DOT__Imp_LF_Imp_AExp_bexp

-- optimize_0plus_b_test1 is also Admitted in the original
-- optimize_0plus_b (BNot (BGt (APlus (ANum 0) (ANum 4)) (ANum 8))) = (BNot (BGt (ANum 4) (ANum 8)))
axiom Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b__test1 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b
       (Original_LF__DOT__Imp_LF_Imp_AExp_BNot
          (Original_LF__DOT__Imp_LF_Imp_AExp_BGt
             (Original_LF__DOT__Imp_LF_Imp_AExp_APlus (Original_LF__DOT__Imp_LF_Imp_AExp_ANum _0)
                (Original_LF__DOT__Imp_LF_Imp_AExp_ANum (S (S (S (S _0))))))
             (Original_LF__DOT__Imp_LF_Imp_AExp_ANum (S (S (S (S (S (S (S (S _0))))))))))))
    (Original_LF__DOT__Imp_LF_Imp_AExp_BNot
       (Original_LF__DOT__Imp_LF_Imp_AExp_BGt (Original_LF__DOT__Imp_LF_Imp_AExp_ANum (S (S (S (S _0)))))
          (Original_LF__DOT__Imp_LF_Imp_AExp_ANum (S (S (S (S (S (S (S (S _0)))))))))))

-- optimize_0plus_b_test2 is also Admitted in the original
-- optimize_0plus_b (BAnd (BLe (APlus (ANum 0) (ANum 4)) (ANum 5)) BTrue) = BAnd (BLe (ANum 4) (ANum 5)) BTrue
axiom Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b__test2 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b
       (Original_LF__DOT__Imp_LF_Imp_AExp_BAnd
          (Original_LF__DOT__Imp_LF_Imp_AExp_BLe
             (Original_LF__DOT__Imp_LF_Imp_AExp_APlus (Original_LF__DOT__Imp_LF_Imp_AExp_ANum _0)
                (Original_LF__DOT__Imp_LF_Imp_AExp_ANum (S (S (S (S _0))))))
             (Original_LF__DOT__Imp_LF_Imp_AExp_ANum (S (S (S (S (S _0)))))))
          Original_LF__DOT__Imp_LF_Imp_AExp_BTrue))
    (Original_LF__DOT__Imp_LF_Imp_AExp_BAnd
       (Original_LF__DOT__Imp_LF_Imp_AExp_BLe
          (Original_LF__DOT__Imp_LF_Imp_AExp_ANum (S (S (S (S _0)))))
          (Original_LF__DOT__Imp_LF_Imp_AExp_ANum (S (S (S (S (S _0)))))))
       Original_LF__DOT__Imp_LF_Imp_AExp_BTrue)
