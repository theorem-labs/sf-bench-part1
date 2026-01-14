-- Lean 4 translation for optimize_0plus_b_sound and all dependencies

set_option linter.unusedVariables false
set_option autoImplicit false

-- MyTrue as alias for Lean's True (Prop in Lean becomes SProp in Rocq)
def MyTrue : Prop := _root_.True
def True_intro : MyTrue := _root_.True.intro

-- Equality in Prop (exported as SProp) - for Type arguments
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality for Prop arguments (also exported as SProp)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- Boolean type (named mybool to avoid conflict with Lean's Bool)
inductive mybool : Type where
  | true : mybool
  | false : mybool

def mybool_true : mybool := mybool.true
def mybool_false : mybool := mybool.false

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def nat_O : nat := nat.O
def nat_S : nat → nat := nat.S

-- Addition on nat
def Nat_add : nat → nat → nat
  | nat.O, n => n
  | nat.S m, n => nat.S (Nat_add m n)

-- Subtraction (truncated)
def Nat_sub : nat → nat → nat
  | nat.O, _ => nat.O
  | nat.S n, nat.O => nat.S n
  | nat.S n, nat.S m => Nat_sub n m

-- Multiplication
def Nat_mul : nat → nat → nat
  | nat.O, _ => nat.O
  | nat.S m, n => Nat_add n (Nat_mul m n)

-- Nat equality comparison
def Nat_eqb : nat → nat → mybool
  | nat.O, nat.O => mybool.true
  | nat.O, nat.S _ => mybool.false
  | nat.S _, nat.O => mybool.false
  | nat.S n, nat.S m => Nat_eqb n m

-- Nat less-than-or-equal comparison
def Nat_leb : nat → nat → mybool
  | nat.O, _ => mybool.true
  | nat.S _, nat.O => mybool.false
  | nat.S n, nat.S m => Nat_leb n m

-- Boolean negation
def negb : mybool → mybool
  | mybool.true => mybool.false
  | mybool.false => mybool.true

-- Boolean conjunction
def andb : mybool → mybool → mybool
  | mybool.true, b => b
  | mybool.false, _ => mybool.false

-- Arithmetic expressions
inductive Original_LF__DOT__Imp_LF_Imp_AExp_aexp : Type where
  | ANum : nat → Original_LF__DOT__Imp_LF_Imp_AExp_aexp
  | APlus : Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp
  | AMinus : Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp
  | AMult : Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp

def Original_LF__DOT__Imp_LF_Imp_AExp_ANum := Original_LF__DOT__Imp_LF_Imp_AExp_aexp.ANum
def Original_LF__DOT__Imp_LF_Imp_AExp_APlus := Original_LF__DOT__Imp_LF_Imp_AExp_aexp.APlus

-- Evaluation function for arithmetic expressions
def Original_LF__DOT__Imp_LF_Imp_AExp_aeval : Original_LF__DOT__Imp_LF_Imp_AExp_aexp → nat
  | Original_LF__DOT__Imp_LF_Imp_AExp_aexp.ANum n => n
  | Original_LF__DOT__Imp_LF_Imp_AExp_aexp.APlus a1 a2 => Nat_add (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a1) (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a2)
  | Original_LF__DOT__Imp_LF_Imp_AExp_aexp.AMinus a1 a2 => Nat_sub (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a1) (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a2)
  | Original_LF__DOT__Imp_LF_Imp_AExp_aexp.AMult a1 a2 => Nat_mul (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a1) (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a2)

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

-- Evaluation function for boolean expressions
def Original_LF__DOT__Imp_LF_Imp_AExp_beval : Original_LF__DOT__Imp_LF_Imp_AExp_bexp → mybool
  | Original_LF__DOT__Imp_LF_Imp_AExp_bexp.BTrue => mybool.true
  | Original_LF__DOT__Imp_LF_Imp_AExp_bexp.BFalse => mybool.false
  | Original_LF__DOT__Imp_LF_Imp_AExp_bexp.BEq a1 a2 =>
      Nat_eqb (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a1) (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a2)
  | Original_LF__DOT__Imp_LF_Imp_AExp_bexp.BNeq a1 a2 =>
      negb (Nat_eqb (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a1) (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a2))
  | Original_LF__DOT__Imp_LF_Imp_AExp_bexp.BLe a1 a2 =>
      Nat_leb (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a1) (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a2)
  | Original_LF__DOT__Imp_LF_Imp_AExp_bexp.BGt a1 a2 =>
      negb (Nat_leb (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a1) (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a2))
  | Original_LF__DOT__Imp_LF_Imp_AExp_bexp.BNot b1 =>
      negb (Original_LF__DOT__Imp_LF_Imp_AExp_beval b1)
  | Original_LF__DOT__Imp_LF_Imp_AExp_bexp.BAnd b1 b2 =>
      andb (Original_LF__DOT__Imp_LF_Imp_AExp_beval b1) (Original_LF__DOT__Imp_LF_Imp_AExp_beval b2)

-- optimize_0plus_b is an axiom in the original (Admitted)
axiom Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b : Original_LF__DOT__Imp_LF_Imp_AExp_bexp → Original_LF__DOT__Imp_LF_Imp_AExp_bexp

-- optimize_0plus_b_sound is also Admitted in the original
axiom Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b__sound :
  ∀ (b : Original_LF__DOT__Imp_LF_Imp_AExp_bexp),
    Corelib_Init_Logic_eq
      (Original_LF__DOT__Imp_LF_Imp_AExp_beval (Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b b))
      (Original_LF__DOT__Imp_LF_Imp_AExp_beval b)
