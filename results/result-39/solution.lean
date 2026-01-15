-- Lean translation of Imp language definitions including ceval_step and ceval__ceval_step

set_option linter.all false

-- True and False in Prop
inductive TrueType : Prop where
  | I : TrueType

def TrueType_I := TrueType.I

inductive FalseType : Prop where

-- Alias for Original.False
def Original_False : Prop := FalseType

-- Define and for export (maps to Prop conjunction)
def and (P Q : Prop) : Prop := P ∧ Q

-- Define and_intro for export
def and_intro {P Q : Prop} (hp : P) (hq : Q) : and P Q := And.intro hp hq

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
inductive or (A B : Prop) : Prop where
  | inl : A → or A B
  | inr : B → or A B

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

-- ===== Logic definitions =====
-- In function from Logic module (using Original.LF_DOT_Poly.LF.Poly.list)
def Original_LF__DOT__Logic_LF_Logic_In {A : Type} (x : A) (l : Original_LF__DOT__Poly_LF_Poly_list A) : Prop :=
  match l with
  | .nil => FalseType
  | .cons x' l' => or (Corelib_Init_Logic_eq x' x) (Original_LF__DOT__Logic_LF_Logic_In x l')

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

-- leb function from LF.Basics  
def Original_LF__DOT__Basics_LF_Basics_leb : nat → nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O, _ => Original_LF__DOT__Basics_LF_Basics_bool.true
  | nat.S _, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S n', nat.S m' => Original_LF__DOT__Basics_LF_Basics_leb n' m'

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

-- ===== re_opt (full optimizer) =====
-- This is the full optimizer from LF.AltAuto that handles more cases
def Original_LF__DOT__AltAuto_LF_AltAuto_re__opt {T : Type} (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  match re with
  | .App _ .EmptySet => .EmptySet
  | .App .EmptyStr re2 => Original_LF__DOT__AltAuto_LF_AltAuto_re__opt re2
  | .App re1 .EmptyStr => Original_LF__DOT__AltAuto_LF_AltAuto_re__opt re1
  | .App re1 re2 => .App (Original_LF__DOT__AltAuto_LF_AltAuto_re__opt re1) (Original_LF__DOT__AltAuto_LF_AltAuto_re__opt re2)
  | .Union .EmptySet re2 => Original_LF__DOT__AltAuto_LF_AltAuto_re__opt re2
  | .Union re1 .EmptySet => Original_LF__DOT__AltAuto_LF_AltAuto_re__opt re1
  | .Union re1 re2 => .Union (Original_LF__DOT__AltAuto_LF_AltAuto_re__opt re1) (Original_LF__DOT__AltAuto_LF_AltAuto_re__opt re2)
  | .Star .EmptySet => .EmptyStr
  | .Star .EmptyStr => .EmptyStr
  | .Star r => .Star (Original_LF__DOT__AltAuto_LF_AltAuto_re__opt r)
  | .EmptySet => .EmptySet
  | .EmptyStr => .EmptyStr
  | .Char x => .Char x

-- Eta-expansion lemmas for re_opt to connect Lean and Rocq recursion schemes
-- These prove that re_opt satisfies its defining equations

theorem re_opt_EmptySet {T : Type} :
  @Original_LF__DOT__AltAuto_LF_AltAuto_re__opt T .EmptySet = .EmptySet := rfl

theorem re_opt_EmptyStr {T : Type} :
  @Original_LF__DOT__AltAuto_LF_AltAuto_re__opt T .EmptyStr = .EmptyStr := rfl

theorem re_opt_Char {T : Type} (x : T) :
  Original_LF__DOT__AltAuto_LF_AltAuto_re__opt (.Char x) = .Char x := rfl

theorem re_opt_App_EmptySet {T : Type} (re1 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) :
  Original_LF__DOT__AltAuto_LF_AltAuto_re__opt (.App re1 .EmptySet) = .EmptySet := by
  cases re1 <;> rfl

theorem re_opt_App_EmptyStr_l {T : Type} (re2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) :
  Original_LF__DOT__AltAuto_LF_AltAuto_re__opt (.App .EmptyStr re2) =
    Original_LF__DOT__AltAuto_LF_AltAuto_re__opt re2 := by
  cases re2 <;> rfl

-- App re1 EmptyStr when re1 is not EmptyStr and not (App _ EmptySet)
theorem re_opt_App_EmptyStr_r_Char {T : Type} (t : T) :
  Original_LF__DOT__AltAuto_LF_AltAuto_re__opt (.App (.Char t) .EmptyStr) =
    Original_LF__DOT__AltAuto_LF_AltAuto_re__opt (.Char t) := rfl

theorem re_opt_App_EmptyStr_r_App {T : Type} (r1 r2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) :
  Original_LF__DOT__AltAuto_LF_AltAuto_re__opt (.App (.App r1 r2) .EmptyStr) =
    Original_LF__DOT__AltAuto_LF_AltAuto_re__opt (.App r1 r2) := by
  cases r2 <;> rfl

theorem re_opt_App_EmptyStr_r_Union {T : Type} (r1 r2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) :
  Original_LF__DOT__AltAuto_LF_AltAuto_re__opt (.App (.Union r1 r2) .EmptyStr) =
    Original_LF__DOT__AltAuto_LF_AltAuto_re__opt (.Union r1 r2) := by
  cases r2 <;> rfl

theorem re_opt_App_EmptyStr_r_Star {T : Type} (r : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) :
  Original_LF__DOT__AltAuto_LF_AltAuto_re__opt (.App (.Star r) .EmptyStr) =
    Original_LF__DOT__AltAuto_LF_AltAuto_re__opt (.Star r) := by
  cases r <;> rfl

theorem re_opt_Union_EmptySet_l {T : Type} (re2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) :
  Original_LF__DOT__AltAuto_LF_AltAuto_re__opt (.Union .EmptySet re2) =
    Original_LF__DOT__AltAuto_LF_AltAuto_re__opt re2 := by
  cases re2 <;> rfl

-- Union re1 EmptySet when re1 is not EmptySet
theorem re_opt_Union_EmptySet_r_EmptyStr {T : Type} :
  @Original_LF__DOT__AltAuto_LF_AltAuto_re__opt T (.Union .EmptyStr .EmptySet) =
    Original_LF__DOT__AltAuto_LF_AltAuto_re__opt .EmptyStr := rfl

theorem re_opt_Union_EmptySet_r_Char {T : Type} (t : T) :
  Original_LF__DOT__AltAuto_LF_AltAuto_re__opt (.Union (.Char t) .EmptySet) =
    Original_LF__DOT__AltAuto_LF_AltAuto_re__opt (.Char t) := rfl

theorem re_opt_Union_EmptySet_r_App {T : Type} (r1 r2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) :
  Original_LF__DOT__AltAuto_LF_AltAuto_re__opt (.Union (.App r1 r2) .EmptySet) =
    Original_LF__DOT__AltAuto_LF_AltAuto_re__opt (.App r1 r2) := by
  cases r2 <;> rfl

theorem re_opt_Union_EmptySet_r_Union {T : Type} (r1 r2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) :
  Original_LF__DOT__AltAuto_LF_AltAuto_re__opt (.Union (.Union r1 r2) .EmptySet) =
    Original_LF__DOT__AltAuto_LF_AltAuto_re__opt (.Union r1 r2) := by
  cases r2 <;> rfl

theorem re_opt_Union_EmptySet_r_Star {T : Type} (r : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) :
  Original_LF__DOT__AltAuto_LF_AltAuto_re__opt (.Union (.Star r) .EmptySet) =
    Original_LF__DOT__AltAuto_LF_AltAuto_re__opt (.Star r) := by
  cases r <;> rfl

theorem re_opt_Star_EmptySet {T : Type} :
  @Original_LF__DOT__AltAuto_LF_AltAuto_re__opt T (.Star .EmptySet) = .EmptyStr := rfl

theorem re_opt_Star_EmptyStr {T : Type} :
  @Original_LF__DOT__AltAuto_LF_AltAuto_re__opt T (.Star .EmptyStr) = .EmptyStr := rfl

-- Star general case
theorem re_opt_Star_Char {T : Type} (t : T) :
  Original_LF__DOT__AltAuto_LF_AltAuto_re__opt (.Star (.Char t)) =
    .Star (Original_LF__DOT__AltAuto_LF_AltAuto_re__opt (.Char t)) := rfl

theorem re_opt_Star_App {T : Type} (r1 r2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) :
  Original_LF__DOT__AltAuto_LF_AltAuto_re__opt (.Star (.App r1 r2)) =
    .Star (Original_LF__DOT__AltAuto_LF_AltAuto_re__opt (.App r1 r2)) := by
  cases r2 <;> rfl

theorem re_opt_Star_Union {T : Type} (r1 r2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) :
  Original_LF__DOT__AltAuto_LF_AltAuto_re__opt (.Star (.Union r1 r2)) =
    .Star (Original_LF__DOT__AltAuto_LF_AltAuto_re__opt (.Union r1 r2)) := by
  cases r2 <;> rfl

theorem re_opt_Star_Star {T : Type} (r : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) :
  Original_LF__DOT__AltAuto_LF_AltAuto_re__opt (.Star (.Star r)) =
    .Star (Original_LF__DOT__AltAuto_LF_AltAuto_re__opt (.Star r)) := by
  cases r <;> rfl

-- re_opt_match'' is an Admitted lemma in the original
-- s =~ re -> s =~ re_opt re
axiom Original_LF__DOT__AltAuto_LF_AltAuto_re__opt__match'' : ∀ (T : Type) (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) (s : Original_LF__DOT__Poly_LF_Poly_list T),
  Original_LF__DOT__IndProp_LF_IndProp_exp__match s re → Original_LF__DOT__IndProp_LF_IndProp_exp__match s (Original_LF__DOT__AltAuto_LF_AltAuto_re__opt re)

-- re_opt_match' is the same as re_opt_match'' (also Admitted)
axiom Original_LF__DOT__AltAuto_LF_AltAuto_re__opt__match' : ∀ (T : Type) (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) (s : Original_LF__DOT__Poly_LF_Poly_list T),
  Original_LF__DOT__IndProp_LF_IndProp_exp__match s re → Original_LF__DOT__IndProp_LF_IndProp_exp__match s (Original_LF__DOT__AltAuto_LF_AltAuto_re__opt re)

-- intuition_succeed1: forall P : Prop, P -> P (Admitted in original)
axiom Original_LF__DOT__AltAuto_LF_AltAuto_intuition__succeed1 : ∀ (P : Prop), P → P

-- fold function on lists
def Original_LF__DOT__Poly_LF_Poly_fold {X Y : Type} (f : X → Y → Y) (l : Original_LF__DOT__Poly_LF_Poly_list X) (b : Y) : Y :=
  match l with
  | .nil => b
  | .cons h t => f h (Original_LF__DOT__Poly_LF_Poly_fold f t b)

-- app_assoc: l ++ m ++ n = (l ++ m) ++ n (Admitted in original)  
axiom Original_LF__DOT__Poly_LF_Poly_app__assoc : ∀ (A : Type) (l m n : Original_LF__DOT__Poly_LF_Poly_list A),
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__Poly_LF_Poly_app A l (Original_LF__DOT__Poly_LF_Poly_app A m n))
    (Original_LF__DOT__Poly_LF_Poly_app A (Original_LF__DOT__Poly_LF_Poly_app A l m) n)

-- app_nil_r: l ++ [] = l (Admitted in original)
axiom Original_LF__DOT__Poly_LF_Poly_app__nil__r : ∀ (X : Type) (l : Original_LF__DOT__Poly_LF_Poly_list X),
  Corelib_Init_Logic_eq (Original_LF__DOT__Poly_LF_Poly_app X l (Original_LF__DOT__Poly_LF_Poly_nil X)) l

-- MStar'': forall T (s : list T) (re : reg_exp T), s =~ Star re -> exists ss, s = fold app ss [] /\ forall s', In s' ss -> s' =~ re
axiom Original_LF__DOT__IndProp_LF_IndProp_MStar'' : ∀ (T : Type) (s : Original_LF__DOT__Poly_LF_Poly_list T) (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T),
  Original_LF__DOT__IndProp_LF_IndProp_exp__match s (Original_LF__DOT__IndProp_LF_IndProp_Star re) →
  ex (fun ss : Original_LF__DOT__Poly_LF_Poly_list (Original_LF__DOT__Poly_LF_Poly_list T) =>
    And (Corelib_Init_Logic_eq s (Original_LF__DOT__Poly_LF_Poly_fold (Original_LF__DOT__Poly_LF_Poly_app T) ss (Original_LF__DOT__Poly_LF_Poly_nil T)))
        (∀ (s' : Original_LF__DOT__Poly_LF_Poly_list T), Original_LF__DOT__Logic_LF_Logic_In s' ss → Original_LF__DOT__IndProp_LF_IndProp_exp__match s' re))

-- ===== Maps t_update_same axiom =====
-- t_update_same : forall A (m : total_map A) x, (x !-> m x ; m) = m
axiom Original_LF__DOT__Maps_LF_Maps_t__update__same : ∀ (A : Type) (m : Original_LF__DOT__Maps_LF_Maps_total__map A) (x : String_string),
  Corelib_Init_Logic_eq
    (fun x' => Original_LF__DOT__Maps_LF_Maps_t__update m x (m x) x')
    (fun x' => m x')

-- ===== Auto ceval_deterministic axiom =====
-- ceval_deterministic: forall c st st1 st2, st =[ c ]=> st1 -> st =[ c ]=> st2 -> st1 = st2
axiom Original_LF__DOT__Auto_LF_Auto_ceval__deterministic :
  ∀ (c : Original_LF__DOT__Imp_LF_Imp_com)
    (st st1 st2 : Original_LF__DOT__Imp_LF_Imp_state),
    Original_LF__DOT__Imp_LF_Imp_ceval c st st1 →
    Original_LF__DOT__Imp_LF_Imp_ceval c st st2 →
    Corelib_Init_Logic_eq st1 st2

-- ===== test_leb3 theorem (Admitted in Original.v) =====
-- test_leb3: leb 4 2 = false
axiom Original_LF__DOT__Basics_LF_Basics_test__leb3 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Basics_LF_Basics_leb (nat.S (nat.S (nat.S (nat.S nat.O)))) (nat.S (nat.S nat.O)))
    Original_LF__DOT__Basics_LF_Basics_false

-- ===== In_example_2 theorem (Admitted in Original.v) =====
-- In_example_2: forall n, In n [2; 4] -> exists n', n = 2 * n'
axiom Original_LF__DOT__Logic_LF_Logic_In__example__2 :
  ∀ (n : nat),
    Original_LF__DOT__Logic_LF_Logic_In n 
      (Original_LF__DOT__Poly_LF_Poly_cons nat (nat.S (nat.S nat.O))
        (Original_LF__DOT__Poly_LF_Poly_cons nat (nat.S (nat.S (nat.S (nat.S nat.O))))
          (Original_LF__DOT__Poly_LF_Poly_nil nat))) →
    ex (fun n' : nat => Corelib_Init_Logic_eq n (nat_mul (nat.S (nat.S nat.O)) n'))

-- ===== eqb_list function (Admitted in Original.v) =====
axiom Original_LF__DOT__Logic_LF_Logic_eqb__list :
  ∀ {A : Type}, (A → A → Original_LF__DOT__Basics_LF_Basics_bool) →
    Original_LF__DOT__Poly_LF_Poly_list A → Original_LF__DOT__Poly_LF_Poly_list A → Original_LF__DOT__Basics_LF_Basics_bool

-- ===== eqb_list_true_iff theorem (Admitted in Original.v) =====
axiom Original_LF__DOT__Logic_LF_Logic_eqb__list__true__iff :
  ∀ (A : Type) (eqb : A → A → Original_LF__DOT__Basics_LF_Basics_bool),
    (∀ (a1 a2 : A), iff (Corelib_Init_Logic_eq (eqb a1 a2) Original_LF__DOT__Basics_LF_Basics_true)
                        (Corelib_Init_Logic_eq a1 a2)) →
    ∀ (l1 l2 : Original_LF__DOT__Poly_LF_Poly_list A),
      iff (Corelib_Init_Logic_eq (Original_LF__DOT__Logic_LF_Logic_eqb__list eqb l1 l2) Original_LF__DOT__Basics_LF_Basics_true)
          (Corelib_Init_Logic_eq l1 l2)

-- ===== ProofObjects definitions =====
-- or in ProofObjects.Props
inductive Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or (P Q : Prop) : Prop where
  | or_introl : P → Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or P Q
  | or_intror : Q → Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or P Q

-- ex in ProofObjects.Props
inductive Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex {A : Type} (P : A → Prop) : Prop where
  | ex_intro : ∀ (x : A), P x → Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex P

-- dist_exists_or_term: (exists x, P x \/ Q x) -> (exists x, P x) \/ (exists x, Q x)
def Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_dist__exists__or__term
    {X : Type} (P Q : X → Prop)
    (H : Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex (fun x => Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or (P x) (Q x)))
    : Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or
        (Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex P)
        (Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex Q) :=
  match H with
  | .ex_intro x pf =>
    match pf with
    | .or_introl hp => .or_introl (.ex_intro x hp)
    | .or_intror hq => .or_intror (.ex_intro x hq)

-- add1 function from ProofObjects
def Original_LF__DOT__ProofObjects_LF_ProofObjects_add1 (n : nat) : nat := nat.S n

-- ===== Tactics definitions =====
-- split_combine_statement is Admitted, so it's an axiom
axiom Original_LF__DOT__Tactics_LF_Tactics_split__combine__statement : Prop

-- split_combine is the theorem
axiom Original_LF__DOT__Tactics_LF_Tactics_split__combine :
  Original_LF__DOT__Tactics_LF_Tactics_split__combine__statement


