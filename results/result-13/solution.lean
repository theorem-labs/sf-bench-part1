-- Lean translation of Imp language definitions including ceval_step and ceval__ceval_step

set_option linter.all false

-- True and False in Prop
inductive TrueType : Prop where
  | I : TrueType

def TrueType_I := TrueType.I

inductive FalseType : Prop where

-- Define our own bool type with names that won't conflict  
inductive mybool : Type where
  | mytrue : mybool
  | myfalse : mybool

-- Aliases for the checker - these become Imported.mybool_mytrue, etc.
def mybool_mytrue : mybool := mybool.mytrue
def mybool_myfalse : mybool := mybool.myfalse
def _true : mybool := mybool.mytrue
def _false : mybool := mybool.myfalse

-- Alias for _bool
def _bool : Type := mybool

-- Define our own nat type
inductive nat : Type where
  | O : nat
  | S : nat → nat

-- Aliases that will become Imported.nat, etc.
def nat_O := nat.O
def nat_S := nat.S
def S := nat.S
def O := nat.O
def _0 := nat.O

-- Nat operations
def nat_add : nat → nat → nat
  | nat.O, m => m
  | nat.S n, m => nat.S (nat_add n m)

def nat_sub : nat → nat → nat
  | n, nat.O => n
  | nat.O, nat.S _ => nat.O
  | nat.S n, nat.S m => nat_sub n m

def nat_mul : nat → nat → nat
  | nat.O, _ => nat.O
  | nat.S n, m => nat_add m (nat_mul n m)

def nat_pred : nat → nat
  | nat.O => nat.O
  | nat.S n => n

-- Aliases for checker
def Nat_add := nat_add
def Nat_sub := nat_sub
def Nat_mul := nat_mul
def Nat_pred := nat_pred

def nat_eqb : nat → nat → mybool
  | nat.O, nat.O => mybool.mytrue
  | nat.S n, nat.S m => nat_eqb n m
  | _, _ => mybool.myfalse

def nat_leb : nat → nat → mybool
  | nat.O, _ => mybool.mytrue
  | nat.S _, nat.O => mybool.myfalse
  | nat.S n, nat.S m => nat_leb n m

def bool_negb : mybool → mybool
  | mybool.mytrue => mybool.myfalse
  | mybool.myfalse => mybool.mytrue

def bool_andb : mybool → mybool → mybool
  | mybool.mytrue, b => b
  | mybool.myfalse, _ => mybool.myfalse

-- Option type
inductive option (A : Type) : Type where
  | None : option A
  | Some : A → option A

def None := @option.None
def Some := @option.Some

-- Product type
inductive prod (A B : Type) : Type where
  | pair : A → B → prod A B

def pair := @prod.pair

-- List type
inductive list (A : Type) : Type where
  | nil : list A
  | cons : A → list A → list A

def nil := @list.nil
def cons := @list.cons

-- Or type (disjunction)
-- or as a structure
structure or (A B : Prop) : Prop where
  intro ::
  elim : ∀ C : Prop, (A → C) → (B → C) → C

-- Logic_not (negation)
def Logic_not (A : Prop) : Prop := A → FalseType

-- Define Ascii as 8 bools (like Rocq's Ascii.ascii)
inductive Ascii_ascii : Type where
  | Ascii : mybool → mybool → mybool → mybool → mybool → mybool → mybool → mybool → Ascii_ascii

-- Alias for checker compatibility  
def Ascii := Ascii_ascii
def Ascii_Ascii := Ascii_ascii.Ascii

-- Define equality on bools
def bool_eqb : mybool → mybool → mybool
  | mybool.mytrue, mybool.mytrue => mybool.mytrue
  | mybool.myfalse, mybool.myfalse => mybool.mytrue
  | _, _ => mybool.myfalse

-- Define equality on Ascii
def Ascii_eqb : Ascii_ascii → Ascii_ascii → mybool
  | Ascii_ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7, Ascii_ascii.Ascii c0 c1 c2 c3 c4 c5 c6 c7 =>
    bool_andb (bool_eqb b0 c0)
      (bool_andb (bool_eqb b1 c1)
        (bool_andb (bool_eqb b2 c2)
          (bool_andb (bool_eqb b3 c3)
            (bool_andb (bool_eqb b4 c4)
              (bool_andb (bool_eqb b5 c5)
                (bool_andb (bool_eqb b6 c6)
                  (bool_eqb b7 c7)))))))

-- String type (like Rocq's String.string)
inductive String_string : Type where
  | EmptyString : String_string
  | String : Ascii_ascii → String_string → String_string

-- Alias for EmptyString
def String_EmptyString : String_string := String_string.EmptyString
def String_String : Ascii_ascii → String_string → String_string := String_string.String

-- String equality
def String_eqb : String_string → String_string → mybool
  | String_string.EmptyString, String_string.EmptyString => mybool.mytrue
  | String_string.String c1 s1, String_string.String c2 s2 =>
    bool_andb (Ascii_eqb c1 c2) (String_eqb s1 s2)
  | _, _ => mybool.myfalse

-- Helper to make an ASCII character from 8 bools
-- ASCII "X" = 88 = 0x58 = 01011000 (little endian: false false false true true false true false)
def char_X : Ascii_ascii := Ascii_ascii.Ascii mybool.myfalse mybool.myfalse mybool.myfalse mybool.mytrue mybool.mytrue mybool.myfalse mybool.mytrue mybool.myfalse
-- ASCII "Y" = 89 = 0x59 = 01011001 (little endian: true false false true true false true false)
def char_Y : Ascii_ascii := Ascii_ascii.Ascii mybool.mytrue mybool.myfalse mybool.myfalse mybool.mytrue mybool.mytrue mybool.myfalse mybool.mytrue mybool.myfalse
-- ASCII "Z" = 90 = 0x5A = 01011010 (little endian: false true false true true false true false)
def char_Z : Ascii_ascii := Ascii_ascii.Ascii mybool.myfalse mybool.mytrue mybool.myfalse mybool.mytrue mybool.mytrue mybool.myfalse mybool.mytrue mybool.myfalse

-- String constants X, Y, Z
def Original_LF__DOT__Imp_LF_Imp_X : String_string := String_string.String char_X String_string.EmptyString
def Original_LF__DOT__Imp_LF_Imp_Y : String_string := String_string.String char_Y String_string.EmptyString
def Original_LF__DOT__Imp_LF_Imp_Z : String_string := String_string.String char_Z String_string.EmptyString

-- Helper: build a nat literal (3)
def nat3 : nat := nat.S (nat.S (nat.S nat.O))
-- Helper: build a nat literal (2) 
def nat2 : nat := nat.S (nat.S nat.O)

-- total_map type (function from string to A)
def Original_LF__DOT__Maps_LF_Maps_total__map (A : Type) := String_string → A

-- t_empty function  
def Original_LF__DOT__Maps_LF_Maps_t__empty {A : Type} (v : A) : Original_LF__DOT__Maps_LF_Maps_total__map A :=
  fun _ => v

-- t_update function
def Original_LF__DOT__Maps_LF_Maps_t__update {A : Type} (m : Original_LF__DOT__Maps_LF_Maps_total__map A)
    (x : String_string) (v : A) : Original_LF__DOT__Maps_LF_Maps_total__map A :=
  fun x' => match String_eqb x x' with
    | mybool.mytrue => v
    | mybool.myfalse => m x'

-- State is total_map nat
def Original_LF__DOT__Imp_LF_Imp_state := Original_LF__DOT__Maps_LF_Maps_total__map nat

-- empty_st: the empty state (all variables map to 0)
def Original_LF__DOT__Imp_LF_Imp_empty__st : Original_LF__DOT__Imp_LF_Imp_state := 
  Original_LF__DOT__Maps_LF_Maps_t__empty nat.O

-- Arithmetic expressions (matches Original.LF_DOT_Imp.LF.Imp.aexp)
inductive Original_LF__DOT__Imp_LF_Imp_aexp : Type where
  | ANum : nat → Original_LF__DOT__Imp_LF_Imp_aexp
  | AId : String_string → Original_LF__DOT__Imp_LF_Imp_aexp
  | APlus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp
  | AMinus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp
  | AMult : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp

-- example_aexp: 3 + (X * 2)
def Original_LF__DOT__Imp_LF_Imp_example__aexp : Original_LF__DOT__Imp_LF_Imp_aexp :=
  Original_LF__DOT__Imp_LF_Imp_aexp.APlus 
    (Original_LF__DOT__Imp_LF_Imp_aexp.ANum nat3)
    (Original_LF__DOT__Imp_LF_Imp_aexp.AMult 
      (Original_LF__DOT__Imp_LF_Imp_aexp.AId Original_LF__DOT__Imp_LF_Imp_X)
      (Original_LF__DOT__Imp_LF_Imp_aexp.ANum nat2))

-- Boolean expressions (matches Original.LF_DOT_Imp.LF.Imp.bexp)
inductive Original_LF__DOT__Imp_LF_Imp_bexp : Type where
  | BTrue : Original_LF__DOT__Imp_LF_Imp_bexp
  | BFalse : Original_LF__DOT__Imp_LF_Imp_bexp
  | BEq : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BNeq : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BLe : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BGt : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BNot : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BAnd : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp

-- Commands (matches Original.LF_DOT_Imp.LF.Imp.com)
inductive Original_LF__DOT__Imp_LF_Imp_com : Type where
  | CSkip : Original_LF__DOT__Imp_LF_Imp_com
  | CAsgn : String_string → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_com
  | CSeq : Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com
  | CIf : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com
  | CWhile : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com

-- Constructor aliases for the checkers
-- Aliases for aexp constructors
def Original_LF__DOT__Imp_LF_Imp_ANum := Original_LF__DOT__Imp_LF_Imp_aexp.ANum
def Original_LF__DOT__Imp_LF_Imp_AId := Original_LF__DOT__Imp_LF_Imp_aexp.AId
def Original_LF__DOT__Imp_LF_Imp_APlus := Original_LF__DOT__Imp_LF_Imp_aexp.APlus
def Original_LF__DOT__Imp_LF_Imp_AMinus := Original_LF__DOT__Imp_LF_Imp_aexp.AMinus
def Original_LF__DOT__Imp_LF_Imp_AMult := Original_LF__DOT__Imp_LF_Imp_aexp.AMult

-- Aliases for bexp constructors
def Original_LF__DOT__Imp_LF_Imp_BTrue := Original_LF__DOT__Imp_LF_Imp_bexp.BTrue
def Original_LF__DOT__Imp_LF_Imp_BFalse := Original_LF__DOT__Imp_LF_Imp_bexp.BFalse
def Original_LF__DOT__Imp_LF_Imp_BEq := Original_LF__DOT__Imp_LF_Imp_bexp.BEq
def Original_LF__DOT__Imp_LF_Imp_BNeq := Original_LF__DOT__Imp_LF_Imp_bexp.BNeq
def Original_LF__DOT__Imp_LF_Imp_BLe := Original_LF__DOT__Imp_LF_Imp_bexp.BLe
def Original_LF__DOT__Imp_LF_Imp_BGt := Original_LF__DOT__Imp_LF_Imp_bexp.BGt
def Original_LF__DOT__Imp_LF_Imp_BNot := Original_LF__DOT__Imp_LF_Imp_bexp.BNot
def Original_LF__DOT__Imp_LF_Imp_BAnd := Original_LF__DOT__Imp_LF_Imp_bexp.BAnd

-- Aliases for com constructors
def Original_LF__DOT__Imp_LF_Imp_CSkip := Original_LF__DOT__Imp_LF_Imp_com.CSkip
def Original_LF__DOT__Imp_LF_Imp_CAsgn := Original_LF__DOT__Imp_LF_Imp_com.CAsgn
def Original_LF__DOT__Imp_LF_Imp_CSeq := Original_LF__DOT__Imp_LF_Imp_com.CSeq
def Original_LF__DOT__Imp_LF_Imp_CIf := Original_LF__DOT__Imp_LF_Imp_com.CIf
def Original_LF__DOT__Imp_LF_Imp_CWhile := Original_LF__DOT__Imp_LF_Imp_com.CWhile

-- aeval: evaluates arithmetic expression in a state
def Original_LF__DOT__Imp_LF_Imp_aeval (st : Original_LF__DOT__Imp_LF_Imp_state) : Original_LF__DOT__Imp_LF_Imp_aexp → nat
  | Original_LF__DOT__Imp_LF_Imp_aexp.ANum n => n
  | Original_LF__DOT__Imp_LF_Imp_aexp.AId x => st x
  | Original_LF__DOT__Imp_LF_Imp_aexp.APlus a1 a2 => nat_add (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
  | Original_LF__DOT__Imp_LF_Imp_aexp.AMinus a1 a2 => nat_sub (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
  | Original_LF__DOT__Imp_LF_Imp_aexp.AMult a1 a2 => nat_mul (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)

-- beval: evaluates boolean expression in a state
def Original_LF__DOT__Imp_LF_Imp_beval (st : Original_LF__DOT__Imp_LF_Imp_state) : Original_LF__DOT__Imp_LF_Imp_bexp → mybool
  | Original_LF__DOT__Imp_LF_Imp_bexp.BTrue => mybool.mytrue
  | Original_LF__DOT__Imp_LF_Imp_bexp.BFalse => mybool.myfalse
  | Original_LF__DOT__Imp_LF_Imp_bexp.BEq a1 a2 => nat_eqb (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
  | Original_LF__DOT__Imp_LF_Imp_bexp.BNeq a1 a2 => bool_negb (nat_eqb (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2))
  | Original_LF__DOT__Imp_LF_Imp_bexp.BLe a1 a2 => nat_leb (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
  | Original_LF__DOT__Imp_LF_Imp_bexp.BGt a1 a2 => bool_negb (nat_leb (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2))
  | Original_LF__DOT__Imp_LF_Imp_bexp.BNot b1 => bool_negb (Original_LF__DOT__Imp_LF_Imp_beval st b1)
  | Original_LF__DOT__Imp_LF_Imp_bexp.BAnd b1 b2 => bool_andb (Original_LF__DOT__Imp_LF_Imp_beval st b1) (Original_LF__DOT__Imp_LF_Imp_beval st b2)

-- ceval: the big-step operational semantics for Imp as an inductive predicate
inductive Original_LF__DOT__Imp_LF_Imp_ceval : Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_state → Original_LF__DOT__Imp_LF_Imp_state → Prop where
  | E_Skip : ∀ st, Original_LF__DOT__Imp_LF_Imp_ceval Original_LF__DOT__Imp_LF_Imp_com.CSkip st st
  | E_Asgn : ∀ st a n x,
      Original_LF__DOT__Imp_LF_Imp_aeval st a = n →
      Original_LF__DOT__Imp_LF_Imp_ceval (Original_LF__DOT__Imp_LF_Imp_com.CAsgn x a) st (Original_LF__DOT__Maps_LF_Maps_t__update st x n)
  | E_Seq : ∀ c1 c2 st st' st'',
      Original_LF__DOT__Imp_LF_Imp_ceval c1 st st' →
      Original_LF__DOT__Imp_LF_Imp_ceval c2 st' st'' →
      Original_LF__DOT__Imp_LF_Imp_ceval (Original_LF__DOT__Imp_LF_Imp_com.CSeq c1 c2) st st''
  | E_IfTrue : ∀ st st' b c1 c2,
      Original_LF__DOT__Imp_LF_Imp_beval st b = mybool.mytrue →
      Original_LF__DOT__Imp_LF_Imp_ceval c1 st st' →
      Original_LF__DOT__Imp_LF_Imp_ceval (Original_LF__DOT__Imp_LF_Imp_com.CIf b c1 c2) st st'
  | E_IfFalse : ∀ st st' b c1 c2,
      Original_LF__DOT__Imp_LF_Imp_beval st b = mybool.myfalse →
      Original_LF__DOT__Imp_LF_Imp_ceval c2 st st' →
      Original_LF__DOT__Imp_LF_Imp_ceval (Original_LF__DOT__Imp_LF_Imp_com.CIf b c1 c2) st st'
  | E_WhileFalse : ∀ b st c,
      Original_LF__DOT__Imp_LF_Imp_beval st b = mybool.myfalse →
      Original_LF__DOT__Imp_LF_Imp_ceval (Original_LF__DOT__Imp_LF_Imp_com.CWhile b c) st st
  | E_WhileTrue : ∀ st st' st'' b c,
      Original_LF__DOT__Imp_LF_Imp_beval st b = mybool.mytrue →
      Original_LF__DOT__Imp_LF_Imp_ceval c st st' →
      Original_LF__DOT__Imp_LF_Imp_ceval (Original_LF__DOT__Imp_LF_Imp_com.CWhile b c) st' st'' →
      Original_LF__DOT__Imp_LF_Imp_ceval (Original_LF__DOT__Imp_LF_Imp_com.CWhile b c) st st''

-- Note: TrueType already defined at top of file

-- Equality type in Prop (will become SProp in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} (a : A) : A → Prop
| refl : Corelib_Init_Logic_eq a a

-- Equality type for Prop arguments (will become SProp -> SProp in Rocq)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} (a : A) : A → Prop
| refl : Corelib_Init_Logic_eq_Prop a a

-- List_In (membership predicate)
def List_In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | list.nil => FalseType
  | list.cons x' l' => or (Corelib_Init_Logic_eq x' x) (List_In x l')

-- Existential quantifier
inductive ex {A : Type} (P : A → Prop) : Prop where
  | intro (w : A) (h : P w) : ex P

def ex_intro := @ex.intro

-- Iff type (logical biconditional)
structure iff (A B : Prop) : Prop where
  mp : A → B
  mpr : B → A

def iff_intro {A B : Prop} (mp : A → B) (mpr : B → A) : iff A B := ⟨mp, mpr⟩

-- or_assoc: admitted axiom
axiom Original_LF__DOT__Logic_LF_Logic_or__assoc : ∀ P Q R : Prop, iff (or P (or Q R)) (or (or P Q) R)

-- ceval_step1: evaluation without fuel (ignores while loops)
def Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step1 
    (st : Original_LF__DOT__Imp_LF_Imp_state) 
    (c : Original_LF__DOT__Imp_LF_Imp_com) : Original_LF__DOT__Imp_LF_Imp_state :=
  match c with
  | Original_LF__DOT__Imp_LF_Imp_com.CSkip => st
  | Original_LF__DOT__Imp_LF_Imp_com.CAsgn x a => 
      Original_LF__DOT__Maps_LF_Maps_t__update st x (Original_LF__DOT__Imp_LF_Imp_aeval st a)
  | Original_LF__DOT__Imp_LF_Imp_com.CSeq c1 c2 =>
      let st' := Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step1 st c1
      Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step1 st' c2
  | Original_LF__DOT__Imp_LF_Imp_com.CIf b c1 c2 =>
      match Original_LF__DOT__Imp_LF_Imp_beval st b with
      | mybool.mytrue => Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step1 st c1
      | mybool.myfalse => Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step1 st c2
  | Original_LF__DOT__Imp_LF_Imp_com.CWhile _ _ => st

-- Reduction equations for ceval_step1
theorem ceval_step1_eq_CSkip (st : Original_LF__DOT__Imp_LF_Imp_state) :
  Corelib_Init_Logic_eq (Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step1 st Original_LF__DOT__Imp_LF_Imp_com.CSkip) st := 
  Corelib_Init_Logic_eq.refl

theorem ceval_step1_eq_CAsgn (st : Original_LF__DOT__Imp_LF_Imp_state) (x : String_string) (a : Original_LF__DOT__Imp_LF_Imp_aexp) :
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step1 st (Original_LF__DOT__Imp_LF_Imp_com.CAsgn x a))
    (Original_LF__DOT__Maps_LF_Maps_t__update st x (Original_LF__DOT__Imp_LF_Imp_aeval st a)) := 
  Corelib_Init_Logic_eq.refl

theorem ceval_step1_eq_CSeq (st : Original_LF__DOT__Imp_LF_Imp_state) (c1 c2 : Original_LF__DOT__Imp_LF_Imp_com) :
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step1 st (Original_LF__DOT__Imp_LF_Imp_com.CSeq c1 c2))
    (Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step1 (Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step1 st c1) c2) := 
  Corelib_Init_Logic_eq.refl

-- Simpler approach: prove the CIf reduction using match_eq
theorem ceval_step1_eq_CIf_true (st : Original_LF__DOT__Imp_LF_Imp_state) (b : Original_LF__DOT__Imp_LF_Imp_bexp) (c1 c2 : Original_LF__DOT__Imp_LF_Imp_com)
  (h : Original_LF__DOT__Imp_LF_Imp_beval st b = mybool.mytrue) :
  Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step1 st (Original_LF__DOT__Imp_LF_Imp_com.CIf b c1 c2) =
  Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step1 st c1 := by
  simp only [Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step1, h]

theorem ceval_step1_eq_CIf_false (st : Original_LF__DOT__Imp_LF_Imp_state) (b : Original_LF__DOT__Imp_LF_Imp_bexp) (c1 c2 : Original_LF__DOT__Imp_LF_Imp_com)
  (h : Original_LF__DOT__Imp_LF_Imp_beval st b = mybool.myfalse) :
  Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step1 st (Original_LF__DOT__Imp_LF_Imp_com.CIf b c1 c2) =
  Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step1 st c2 := by
  simp only [Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step1, h]

theorem ceval_step1_eq_CWhile (st : Original_LF__DOT__Imp_LF_Imp_state) (b : Original_LF__DOT__Imp_LF_Imp_bexp) (c : Original_LF__DOT__Imp_LF_Imp_com) :
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step1 st (Original_LF__DOT__Imp_LF_Imp_com.CWhile b c))
    st := 
  Corelib_Init_Logic_eq.refl

-- ceval_fun_no_while is the same as ceval_step1
def Original_LF__DOT__Imp_LF_Imp_ceval__fun__no__while 
    (st : Original_LF__DOT__Imp_LF_Imp_state) 
    (c : Original_LF__DOT__Imp_LF_Imp_com) : Original_LF__DOT__Imp_LF_Imp_state :=
  match c with
  | Original_LF__DOT__Imp_LF_Imp_com.CSkip => st
  | Original_LF__DOT__Imp_LF_Imp_com.CAsgn x a => 
      Original_LF__DOT__Maps_LF_Maps_t__update st x (Original_LF__DOT__Imp_LF_Imp_aeval st a)
  | Original_LF__DOT__Imp_LF_Imp_com.CSeq c1 c2 =>
      let st' := Original_LF__DOT__Imp_LF_Imp_ceval__fun__no__while st c1
      Original_LF__DOT__Imp_LF_Imp_ceval__fun__no__while st' c2
  | Original_LF__DOT__Imp_LF_Imp_com.CIf b c1 c2 =>
      match Original_LF__DOT__Imp_LF_Imp_beval st b with
      | mybool.mytrue => Original_LF__DOT__Imp_LF_Imp_ceval__fun__no__while st c1
      | mybool.myfalse => Original_LF__DOT__Imp_LF_Imp_ceval__fun__no__while st c2
  | Original_LF__DOT__Imp_LF_Imp_com.CWhile _ _ => st

-- Reduction equations for ceval_fun_no_while (provable by rfl)
theorem ceval_fun_no_while_eq_CSkip (st : Original_LF__DOT__Imp_LF_Imp_state) :
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__Imp_LF_Imp_ceval__fun__no__while st Original_LF__DOT__Imp_LF_Imp_com.CSkip)
    st := Corelib_Init_Logic_eq.refl

theorem ceval_fun_no_while_eq_CAsgn (st : Original_LF__DOT__Imp_LF_Imp_state) 
    (x : String_string) (a : Original_LF__DOT__Imp_LF_Imp_aexp) :
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__Imp_LF_Imp_ceval__fun__no__while st (Original_LF__DOT__Imp_LF_Imp_com.CAsgn x a))
    (Original_LF__DOT__Maps_LF_Maps_t__update st x (Original_LF__DOT__Imp_LF_Imp_aeval st a)) := 
  Corelib_Init_Logic_eq.refl

theorem ceval_fun_no_while_eq_CSeq (st : Original_LF__DOT__Imp_LF_Imp_state)
    (c1 c2 : Original_LF__DOT__Imp_LF_Imp_com) :
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__Imp_LF_Imp_ceval__fun__no__while st (Original_LF__DOT__Imp_LF_Imp_com.CSeq c1 c2))
    (Original_LF__DOT__Imp_LF_Imp_ceval__fun__no__while 
      (Original_LF__DOT__Imp_LF_Imp_ceval__fun__no__while st c1) c2) := 
  Corelib_Init_Logic_eq.refl

-- CIf case - we can only say what it equals via the match eliminator
theorem ceval_fun_no_while_eq_CIf (st : Original_LF__DOT__Imp_LF_Imp_state)
    (b : Original_LF__DOT__Imp_LF_Imp_bexp) (c1 c2 : Original_LF__DOT__Imp_LF_Imp_com) :
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__Imp_LF_Imp_ceval__fun__no__while st (Original_LF__DOT__Imp_LF_Imp_com.CIf b c1 c2))
    (match Original_LF__DOT__Imp_LF_Imp_beval st b with
     | mybool.mytrue => Original_LF__DOT__Imp_LF_Imp_ceval__fun__no__while st c1
     | mybool.myfalse => Original_LF__DOT__Imp_LF_Imp_ceval__fun__no__while st c2) := 
  Corelib_Init_Logic_eq.refl

theorem ceval_fun_no_while_eq_CWhile (st : Original_LF__DOT__Imp_LF_Imp_state)
    (b : Original_LF__DOT__Imp_LF_Imp_bexp) (c : Original_LF__DOT__Imp_LF_Imp_com) :
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__Imp_LF_Imp_ceval__fun__no__while st (Original_LF__DOT__Imp_LF_Imp_com.CWhile b c))
    st := Corelib_Init_Logic_eq.refl

-- ceval_step: step-indexed evaluation function
def Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step 
    (st : Original_LF__DOT__Imp_LF_Imp_state) 
    (c : Original_LF__DOT__Imp_LF_Imp_com) 
    (i : nat) : option Original_LF__DOT__Imp_LF_Imp_state :=
  match i with
  | nat.O => option.None
  | nat.S i' =>
    match c with
    | Original_LF__DOT__Imp_LF_Imp_com.CSkip => 
        option.Some st
    | Original_LF__DOT__Imp_LF_Imp_com.CAsgn x a => 
        option.Some (Original_LF__DOT__Maps_LF_Maps_t__update st x (Original_LF__DOT__Imp_LF_Imp_aeval st a))
    | Original_LF__DOT__Imp_LF_Imp_com.CSeq c1 c2 =>
        match Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step st c1 i' with
        | option.Some st' => Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step st' c2 i'
        | option.None => option.None
    | Original_LF__DOT__Imp_LF_Imp_com.CIf b c1 c2 =>
        match Original_LF__DOT__Imp_LF_Imp_beval st b with
        | mybool.mytrue => Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step st c1 i'
        | mybool.myfalse => Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step st c2 i'
    | Original_LF__DOT__Imp_LF_Imp_com.CWhile b c1 =>
        match Original_LF__DOT__Imp_LF_Imp_beval st b with
        | mybool.mytrue =>
            match Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step st c1 i' with
            | option.Some st' => Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step st' c i'
            | option.None => option.None
        | mybool.myfalse => option.Some st

-- test_ceval function (500 steps)
-- Building nat10 as S applied 10 times
def nat10 : nat := nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))))))
-- nat100 = 10 * 10
def nat100 : nat := nat_add (nat_add (nat_add (nat_add (nat_add (nat_add (nat_add (nat_add (nat_add nat10 nat10) nat10) nat10) nat10) nat10) nat10) nat10) nat10) nat10
-- nat500 = 5 * 100
def nat500 : nat := nat_add (nat_add (nat_add (nat_add nat100 nat100) nat100) nat100) nat100

def Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_test__ceval 
    (st : Original_LF__DOT__Imp_LF_Imp_state) 
    (c : Original_LF__DOT__Imp_LF_Imp_com) 
    : option (prod (prod nat nat) nat) :=
  match Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step st c nat500 with
  | option.None => option.None
  | option.Some st' => option.Some (prod.pair (prod.pair (st' Original_LF__DOT__Imp_LF_Imp_X) (st' Original_LF__DOT__Imp_LF_Imp_Y)) (st' Original_LF__DOT__Imp_LF_Imp_Z))

-- example_test_ceval is Admitted in Original.v
axiom Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_example__test__ceval : 
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_test__ceval 
      Original_LF__DOT__Imp_LF_Imp_empty__st
      (Original_LF__DOT__Imp_LF_Imp_com.CSeq 
        (Original_LF__DOT__Imp_LF_Imp_com.CAsgn Original_LF__DOT__Imp_LF_Imp_X 
          (Original_LF__DOT__Imp_LF_Imp_aexp.ANum (nat.S (nat.S nat.O))))
        (Original_LF__DOT__Imp_LF_Imp_com.CIf 
          (Original_LF__DOT__Imp_LF_Imp_bexp.BLe 
            (Original_LF__DOT__Imp_LF_Imp_aexp.AId Original_LF__DOT__Imp_LF_Imp_X)
            (Original_LF__DOT__Imp_LF_Imp_aexp.ANum (nat.S nat.O)))
          (Original_LF__DOT__Imp_LF_Imp_com.CAsgn Original_LF__DOT__Imp_LF_Imp_Y 
            (Original_LF__DOT__Imp_LF_Imp_aexp.ANum (nat.S (nat.S (nat.S nat.O)))))
          (Original_LF__DOT__Imp_LF_Imp_com.CAsgn Original_LF__DOT__Imp_LF_Imp_Z 
            (Original_LF__DOT__Imp_LF_Imp_aexp.ANum (nat.S (nat.S (nat.S (nat.S nat.O)))))))))
    (option.Some (prod.pair (prod.pair (nat.S (nat.S nat.O)) nat.O) (nat.S (nat.S (nat.S (nat.S nat.O))))))

-- pup_to_n is Admitted in Original.v, so we treat it as an axiom
axiom Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_pup__to__n : Original_LF__DOT__Imp_LF_Imp_com

-- pup_to_n_1 is an admitted example, so we make it an axiom
axiom Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_pup__to__n__1 : 
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_test__ceval 
      (Original_LF__DOT__Maps_LF_Maps_t__update Original_LF__DOT__Imp_LF_Imp_empty__st Original_LF__DOT__Imp_LF_Imp_X 
        (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))) 
      Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_pup__to__n)
    (option.Some (prod.pair (prod.pair nat.O 
      (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))))))))))))) nat.O))

-- The theorem ceval__ceval_step as axiom (it's Admitted in Original)
axiom Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval____ceval__step :
  ∀ (c : Original_LF__DOT__Imp_LF_Imp_com) 
    (st st' : Original_LF__DOT__Imp_LF_Imp_state),
  Original_LF__DOT__Imp_LF_Imp_ceval c st st' →
  ex (fun i : nat => Corelib_Init_Logic_eq (Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step st c i) (option.Some st'))

-- The theorem ceval_and_ceval_step_coincide as axiom (it's Admitted in Original)
axiom Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__and__ceval__step__coincide :
  ∀ (c : Original_LF__DOT__Imp_LF_Imp_com) 
    (st st' : Original_LF__DOT__Imp_LF_Imp_state),
  iff (Original_LF__DOT__Imp_LF_Imp_ceval c st st')
      (ex (fun i : nat => Corelib_Init_Logic_eq (Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step st c i) (option.Some st')))

-- ===== Poly list definitions =====
-- List type (matching Original.LF_DOT_Poly.LF.Poly.list)
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

def Original_LF__DOT__Poly_LF_Poly_cons (X : Type) (x : X) (xs : Original_LF__DOT__Poly_LF_Poly_list X) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons x xs

-- app function for list
def Original_LF__DOT__Poly_LF_Poly_app (X : Type) (l1 l2 : Original_LF__DOT__Poly_LF_Poly_list X) : Original_LF__DOT__Poly_LF_Poly_list X :=
  match l1 with
  | .nil => l2
  | .cons x xs => .cons x (Original_LF__DOT__Poly_LF_Poly_app X xs l2)

-- ===== Basics bool (LF.Basics.bool) =====
-- This is separate from mybool used for Imp
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- even function (matching LF.Basics.even)
def Original_LF__DOT__Basics_LF_Basics_even : nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O => Original_LF__DOT__Basics_LF_Basics_bool.true
  | nat.S nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S (nat.S n') => Original_LF__DOT__Basics_LF_Basics_even n'

-- Helper to build nat from Nat
def natOfNat : Nat → nat
  | 0 => nat.O
  | Nat.succ n => nat.S (natOfNat n)

-- not_even_1001 theorem (admitted in Original.v, so axiom here)
axiom Original_LF__DOT__Logic_LF_Logic_not__even__1001 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Basics_LF_Basics_even (natOfNat 1001))
    Original_LF__DOT__Basics_LF_Basics_false

-- ===== IndProp types =====
-- Regular expression type
inductive Original_LF__DOT__IndProp_LF_IndProp_reg__exp (T : Type) : Type where
  | EmptySet : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | EmptyStr : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Char : T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | App : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Union : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Star : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T

-- Constructor aliases
def Original_LF__DOT__IndProp_LF_IndProp_EmptySet (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptySet

def Original_LF__DOT__IndProp_LF_IndProp_EmptyStr (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptyStr

def Original_LF__DOT__IndProp_LF_IndProp_Char {T : Type} (t : T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Char t

def Original_LF__DOT__IndProp_LF_IndProp_App {T : Type} (r1 r2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.App r1 r2

def Original_LF__DOT__IndProp_LF_IndProp_Union {T : Type} (r1 r2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Union r1 r2

def Original_LF__DOT__IndProp_LF_IndProp_Star {T : Type} (r : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star r

-- EmptyStr' is defined as Star EmptySet
def Original_LF__DOT__IndProp_LF_IndProp_EmptyStr' (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_Star (Original_LF__DOT__IndProp_LF_IndProp_EmptySet T)

-- exp_match inductive type
inductive Original_LF__DOT__IndProp_LF_IndProp_exp__match {T : Type} : Original_LF__DOT__Poly_LF_Poly_list T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Prop where
  | MEmpty : Original_LF__DOT__IndProp_LF_IndProp_exp__match .nil .EmptyStr
  | MChar (x : T) : Original_LF__DOT__IndProp_LF_IndProp_exp__match (.cons x .nil) (.Char x)
  | MApp (s1 s2 : Original_LF__DOT__Poly_LF_Poly_list T) (re1 re2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
         (H1 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s1 re1)
         (H2 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s2 re2) :
         Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_app T s1 s2) (.App re1 re2)
  | MUnionL (s1 : Original_LF__DOT__Poly_LF_Poly_list T) (re1 re2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
            (H1 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s1 re1) :
            Original_LF__DOT__IndProp_LF_IndProp_exp__match s1 (.Union re1 re2)
  | MUnionR (s2 : Original_LF__DOT__Poly_LF_Poly_list T) (re1 re2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
            (H2 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s2 re2) :
            Original_LF__DOT__IndProp_LF_IndProp_exp__match s2 (.Union re1 re2)
  | MStar0 (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) :
           Original_LF__DOT__IndProp_LF_IndProp_exp__match .nil (.Star re)
  | MStarApp (s1 s2 : Original_LF__DOT__Poly_LF_Poly_list T) (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
             (H1 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s1 re)
             (H2 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s2 (.Star re)) :
             Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_app T s1 s2) (.Star re)

-- ===== AltAuto definitions =====
-- re_opt_e (from LF.AltAuto) - Optimizes regular expressions by removing EmptyStr from App
def Original_LF__DOT__AltAuto_LF_AltAuto_re__opt__e {T : Type} (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  match re with
  | .EmptySet => .EmptySet
  | .EmptyStr => .EmptyStr
  | .Char t => .Char t
  | .App .EmptyStr re2 => Original_LF__DOT__AltAuto_LF_AltAuto_re__opt__e re2
  | .App re1 re2 => .App (Original_LF__DOT__AltAuto_LF_AltAuto_re__opt__e re1) (Original_LF__DOT__AltAuto_LF_AltAuto_re__opt__e re2)
  | .Union re1 re2 => .Union (Original_LF__DOT__AltAuto_LF_AltAuto_re__opt__e re1) (Original_LF__DOT__AltAuto_LF_AltAuto_re__opt__e re2)
  | .Star r => .Star (Original_LF__DOT__AltAuto_LF_AltAuto_re__opt__e r)

-- re_opt_e_match axiom (this is an Admitted lemma in the original)
-- s =~ re -> s =~ re_opt_e re
axiom Original_LF__DOT__AltAuto_LF_AltAuto_re__opt__e__match : ∀ (T : Type) (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) (s : Original_LF__DOT__Poly_LF_Poly_list T),
  Original_LF__DOT__IndProp_LF_IndProp_exp__match s re → Original_LF__DOT__IndProp_LF_IndProp_exp__match s (Original_LF__DOT__AltAuto_LF_AltAuto_re__opt__e re)

-- ===== ceval_step3 =====
-- ceval_step3 (same as ceval_step but for different naming)
def Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step3 (st : Original_LF__DOT__Imp_LF_Imp_state) (c : Original_LF__DOT__Imp_LF_Imp_com) (i : nat) : option Original_LF__DOT__Imp_LF_Imp_state :=
  match i with
  | nat.O => option.None
  | nat.S i' =>
    match c with
    | .CSkip => option.Some st
    | .CAsgn l a1 => option.Some (Original_LF__DOT__Maps_LF_Maps_t__update st l (Original_LF__DOT__Imp_LF_Imp_aeval st a1))
    | .CSeq c1 c2 =>
        match Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step3 st c1 i' with
        | option.Some st' => Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step3 st' c2 i'
        | option.None => option.None
    | .CIf b c1 c2 =>
        match Original_LF__DOT__Imp_LF_Imp_beval st b with
        | mybool.mytrue => Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step3 st c1 i'
        | mybool.myfalse => Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step3 st c2 i'
    | .CWhile b c1 =>
        match Original_LF__DOT__Imp_LF_Imp_beval st b with
        | mybool.mytrue =>
            match Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step3 st c1 i' with
            | option.Some st' => Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step3 st' c i'
            | option.None => option.None
        | mybool.myfalse => option.Some st

-- ===== Maps t_update_same axiom =====
-- t_update_same : forall A (m : total_map A) x, (x !-> m x ; m) = m
axiom Original_LF__DOT__Maps_LF_Maps_t__update__same : ∀ (A : Type) (m : Original_LF__DOT__Maps_LF_Maps_total__map A) (x : String_string),
  Corelib_Init_Logic_eq
    (fun x' => Original_LF__DOT__Maps_LF_Maps_t__update m x (m x) x')
    (fun x' => m x')

-- ===== Basics eqb and leb =====
-- eqb function (matching LF.Basics.eqb)
def Original_LF__DOT__Basics_LF_Basics_eqb : nat → nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.true
  | nat.O, nat.S _ => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S _, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S n', nat.S m' => Original_LF__DOT__Basics_LF_Basics_eqb n' m'

-- leb function (matching LF.Basics.leb)
def Original_LF__DOT__Basics_LF_Basics_leb : nat → nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O, _ => Original_LF__DOT__Basics_LF_Basics_bool.true
  | nat.S _, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S n', nat.S m' => Original_LF__DOT__Basics_LF_Basics_leb n' m'

-- nandb function (Admitted in Original.v, so axiom)
axiom Original_LF__DOT__Basics_LF_Basics_nandb : Original_LF__DOT__Basics_LF_Basics_bool → Original_LF__DOT__Basics_LF_Basics_bool → Original_LF__DOT__Basics_LF_Basics_bool

-- test_nandb3 axiom (Admitted in Original.v)
axiom Original_LF__DOT__Basics_LF_Basics_test__nandb3 :
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__Basics_LF_Basics_nandb Original_LF__DOT__Basics_LF_Basics_false Original_LF__DOT__Basics_LF_Basics_true)
    Original_LF__DOT__Basics_LF_Basics_true

-- test_leb2 axiom (Admitted in Original.v)
axiom Original_LF__DOT__Basics_LF_Basics_test__leb2 :
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__Basics_LF_Basics_leb (nat.S (nat.S nat.O)) (nat.S (nat.S (nat.S (nat.S nat.O)))))
    Original_LF__DOT__Basics_LF_Basics_true

-- ===== NatList definitions =====
-- natlist type (custom list of nats)
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natlist : Type where
  | nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist

def Original_LF__DOT__Lists_LF_Lists_NatList_nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil

def Original_LF__DOT__Lists_LF_Lists_NatList_cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons

-- bag is a type alias for natlist
def Original_LF__DOT__Lists_LF_Lists_NatList_bag : Type := Original_LF__DOT__Lists_LF_Lists_NatList_natlist

-- nth_bad: returns 42 for out of bounds
def nat42 : nat := nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))))))))))))))))))))))))))))))))))))))

def Original_LF__DOT__Lists_LF_Lists_NatList_nth__bad : Original_LF__DOT__Lists_LF_Lists_NatList_natlist → nat → nat
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil, _ => nat42
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons a l', n =>
    match n with
    | nat.O => a
    | nat.S n' => Original_LF__DOT__Lists_LF_Lists_NatList_nth__bad l' n'

-- count function (Admitted in Original.v)
axiom Original_LF__DOT__Lists_LF_Lists_NatList_count : nat → Original_LF__DOT__Lists_LF_Lists_NatList_bag → nat

-- remove_all function (Admitted in Original.v)
axiom Original_LF__DOT__Lists_LF_Lists_NatList_remove__all : nat → Original_LF__DOT__Lists_LF_Lists_NatList_bag → Original_LF__DOT__Lists_LF_Lists_NatList_bag

-- test_remove_all3 axiom
-- test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2
axiom Original_LF__DOT__Lists_LF_Lists_NatList_test__remove__all3 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_count (nat.S (nat.S (nat.S (nat.S nat.O))))   -- 4
      (Original_LF__DOT__Lists_LF_Lists_NatList_remove__all (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))  -- 5
        (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S (nat.S nat.O))       -- 2
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S nat.O)             -- 1
            (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S (nat.S (nat.S (nat.S nat.O))))  -- 4
              (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))  -- 5
                (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S nat.O)       -- 1
                  (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S (nat.S (nat.S (nat.S nat.O))))  -- 4
                    Original_LF__DOT__Lists_LF_Lists_NatList_nil))))))))
    (nat.S (nat.S nat.O))  -- 2

-- ===== Church numerals (cnat) =====
-- cnat is Church numerals
def Original_LF__DOT__Poly_LF_Poly_Exercises_cnat : Type 1 := 
  (x : Type) → (x → x) → x → x

-- one : cnat
def Original_LF__DOT__Poly_LF_Poly_Exercises_one : Original_LF__DOT__Poly_LF_Poly_Exercises_cnat :=
  fun (x : Type) (succ : x → x) (zero : x) => succ zero

-- mult : cnat -> cnat -> cnat (Admitted in Original.v)
axiom Original_LF__DOT__Poly_LF_Poly_Exercises_mult : Original_LF__DOT__Poly_LF_Poly_Exercises_cnat → Original_LF__DOT__Poly_LF_Poly_Exercises_cnat → Original_LF__DOT__Poly_LF_Poly_Exercises_cnat

-- Universe-polymorphic equality for Type 1 (for cnat)
inductive Corelib_Init_Logic_eq_Type1 {A : Type 1} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Type1 a a

-- mult_1 : mult one one = one (Admitted in Original.v)
axiom Original_LF__DOT__Poly_LF_Poly_Exercises_mult__1 : 
    Corelib_Init_Logic_eq_Type1 
      (Original_LF__DOT__Poly_LF_Poly_Exercises_mult Original_LF__DOT__Poly_LF_Poly_Exercises_one Original_LF__DOT__Poly_LF_Poly_Exercises_one)
      Original_LF__DOT__Poly_LF_Poly_Exercises_one

-- ===== IndProp reflect =====
-- reflect type (matching LF.IndProp.reflect)
inductive Original_LF__DOT__IndProp_LF_IndProp_reflect (P : Prop) : Original_LF__DOT__Basics_LF_Basics_bool → Prop where
  | ReflectT (H : P) : Original_LF__DOT__IndProp_LF_IndProp_reflect P Original_LF__DOT__Basics_LF_Basics_bool.true
  | ReflectF (H : Logic_not P) : Original_LF__DOT__IndProp_LF_IndProp_reflect P Original_LF__DOT__Basics_LF_Basics_bool.false

-- eqbP : forall n m, reflect (n = m) (n =? m) (Admitted in Original.v)
axiom Original_LF__DOT__IndProp_LF_IndProp_eqbP :
  ∀ (n m : nat), Original_LF__DOT__IndProp_LF_IndProp_reflect 
    (Corelib_Init_Logic_eq n m) 
    (Original_LF__DOT__Basics_LF_Basics_eqb n m)

-- inversion_ex1 : forall n m o, [n; m] = [o; o] -> [n] = [m] (Admitted in Original.v)
axiom Original_LF__DOT__IndProp_LF_IndProp_inversion__ex1 :
  ∀ (n m o : nat),
    Corelib_Init_Logic_eq 
      (Original_LF__DOT__Poly_LF_Poly_cons nat n (Original_LF__DOT__Poly_LF_Poly_cons nat m (Original_LF__DOT__Poly_LF_Poly_nil nat)))
      (Original_LF__DOT__Poly_LF_Poly_cons nat o (Original_LF__DOT__Poly_LF_Poly_cons nat o (Original_LF__DOT__Poly_LF_Poly_nil nat))) →
    Corelib_Init_Logic_eq 
      (Original_LF__DOT__Poly_LF_Poly_cons nat n (Original_LF__DOT__Poly_LF_Poly_nil nat))
      (Original_LF__DOT__Poly_LF_Poly_cons nat m (Original_LF__DOT__Poly_LF_Poly_nil nat))

-- ===== AltAuto match_ex3' =====
-- match_ex3' : forall P : Prop, P -> P (Admitted in Original.v)
axiom Original_LF__DOT__AltAuto_LF_AltAuto_match__ex3' :
  ∀ (P : Prop), P → P

-- ===== Imp XtimesYinZ =====
-- XtimesYinZ : com (defined as Z := X * Y)
def Original_LF__DOT__Imp_LF_Imp_XtimesYinZ : Original_LF__DOT__Imp_LF_Imp_com :=
  Original_LF__DOT__Imp_LF_Imp_com.CAsgn Original_LF__DOT__Imp_LF_Imp_Z
    (Original_LF__DOT__Imp_LF_Imp_aexp.AMult 
      (Original_LF__DOT__Imp_LF_Imp_aexp.AId Original_LF__DOT__Imp_LF_Imp_X)
      (Original_LF__DOT__Imp_LF_Imp_aexp.AId Original_LF__DOT__Imp_LF_Imp_Y))

-- ===== Rel relation =====
-- Definition relation (X: Type) := X -> X -> Prop.
def Original_LF_Rel_relation (X : Type) : Type := X → X → Prop

-- reflexive
def Original_LF_Rel_reflexive (X : Type) (R : Original_LF_Rel_relation X) : Prop :=
  ∀ a : X, R a a

-- transitive
def Original_LF_Rel_transitive (X : Type) (R : Original_LF_Rel_relation X) : Prop :=
  ∀ a b c : X, R a b → R b c → R a c

-- symmetric
def Original_LF_Rel_symmetric (X : Type) (R : Original_LF_Rel_relation X) : Prop :=
  ∀ a b : X, R a b → R b a

-- antisymmetric
def Original_LF_Rel_antisymmetric (X : Type) (R : Original_LF_Rel_relation X) : Prop :=
  ∀ a b : X, R a b → R b a → Corelib_Init_Logic_eq a b




