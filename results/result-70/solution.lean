-- Comprehensive Lean translation for all required isomorphisms
set_option linter.all false

-- ============================================================
-- Basic Types
-- ============================================================

-- Custom bool to avoid Lean stdlib issues
inductive Stdlib_bool : Type where
  | true : Stdlib_bool
  | false : Stdlib_bool

def Stdlib_bool_true := Stdlib_bool.true
def Stdlib_bool_false := Stdlib_bool.false

-- Alias for bool (using Coq_bool to avoid conflict)
def Coq_bool := Stdlib_bool
def Coq_bool_true := Stdlib_bool.true
def Coq_bool_false := Stdlib_bool.false

-- Rocq aliases
def RocqBool := Stdlib_bool
def RocqBool_true := Stdlib_bool.true
def RocqBool_false := Stdlib_bool.false

-- Custom nat
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Addition on nat
def Nat_add : nat → nat → nat
  | nat.O, m => m
  | nat.S p, m => nat.S (Nat_add p m)

-- Subtraction on nat
def Nat_sub : nat → nat → nat
  | n, nat.O => n
  | nat.O, nat.S _ => nat.O
  | nat.S n, nat.S m => Nat_sub n m

-- Multiplication on nat
def Nat_mul : nat → nat → nat
  | nat.O, _ => nat.O
  | nat.S n, m => Nat_add m (Nat_mul n m)

-- pred on nat
def Nat_pred : nat → nat
  | nat.O => nat.O
  | nat.S n => n

-- Nat equality
def Nat_eqb : nat → nat → Stdlib_bool
  | nat.O, nat.O => Stdlib_bool.true
  | nat.S n, nat.S m => Nat_eqb n m
  | _, _ => Stdlib_bool.false

-- Nat less-than-or-equal
def Nat_leb : nat → nat → Stdlib_bool
  | nat.O, _ => Stdlib_bool.true
  | nat.S _, nat.O => Stdlib_bool.false
  | nat.S n, nat.S m => Nat_leb n m

-- lowercase alias
def nat_leb := Nat_leb

-- Bool operations
def negb : Stdlib_bool → Stdlib_bool
  | Stdlib_bool.true => Stdlib_bool.false
  | Stdlib_bool.false => Stdlib_bool.true

def andb : Stdlib_bool → Stdlib_bool → Stdlib_bool
  | Stdlib_bool.true, b => b
  | Stdlib_bool.false, _ => Stdlib_bool.false

def orb : Stdlib_bool → Stdlib_bool → Stdlib_bool
  | Stdlib_bool.true, _ => Stdlib_bool.true
  | Stdlib_bool.false, b => b

def Bool_eqb : Stdlib_bool → Stdlib_bool → Stdlib_bool
  | Stdlib_bool.true, Stdlib_bool.true => Stdlib_bool.true
  | Stdlib_bool.false, Stdlib_bool.false => Stdlib_bool.true
  | _, _ => Stdlib_bool.false

-- ============================================================
-- Ascii and String
-- ============================================================

-- Custom ascii (8 bools)
inductive Ascii_ascii : Type where
  | Ascii : Stdlib_bool → Stdlib_bool → Stdlib_bool → Stdlib_bool → Stdlib_bool → Stdlib_bool → Stdlib_bool → Stdlib_bool → Ascii_ascii

def Ascii_Ascii := Ascii_ascii.Ascii

-- Ascii equality
def Ascii_eqb : Ascii_ascii → Ascii_ascii → Stdlib_bool
  | Ascii_ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7, Ascii_ascii.Ascii c0 c1 c2 c3 c4 c5 c6 c7 =>
    andb (Bool_eqb b0 c0)
      (andb (Bool_eqb b1 c1)
        (andb (Bool_eqb b2 c2)
          (andb (Bool_eqb b3 c3)
            (andb (Bool_eqb b4 c4)
              (andb (Bool_eqb b5 c5)
                (andb (Bool_eqb b6 c6)
                  (Bool_eqb b7 c7)))))))

-- Custom string
inductive String_string : Type where
  | EmptyString : String_string
  | String : Ascii_ascii → String_string → String_string

def String_EmptyString := String_string.EmptyString
def String_String := String_string.String

-- String equality
def String_eqb : String_string → String_string → Stdlib_bool
  | String_string.EmptyString, String_string.EmptyString => Stdlib_bool.true
  | String_string.String c1 s1, String_string.String c2 s2 =>
    andb (Ascii_eqb c1 c2) (String_eqb s1 s2)
  | _, _ => Stdlib_bool.false

-- ============================================================
-- Prop-level types
-- ============================================================

-- Equality in Prop (for Type arguments)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl (A : Type) (a : A) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl a

-- Equality in Prop (for Prop arguments)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

def Corelib_Init_Logic_eq_Prop_refl (A : Prop) (a : A) : Corelib_Init_Logic_eq_Prop a a :=
  Corelib_Init_Logic_eq_Prop.refl a

-- MyTrue (maps to Coq's True)
inductive MyTrue : Prop where
  | intro : MyTrue

def MyTrue_intro : MyTrue := MyTrue.intro

-- MyFalse (maps to Coq's False)
inductive MyFalse : Prop where

-- not
def Logic_not (P : Prop) : Prop := P → MyFalse

-- iff
structure iff (A B : Prop) : Prop where
  mp : A → B
  mpr : B → A

-- ex (existential)
inductive ex {A : Type} (P : A → Prop) : Prop where
  | intro (x : A) (h : P x) : ex P

-- prod
inductive prod (A B : Type) : Type where
  | pair : A → B → prod A B

def prod_pair := @prod.pair

-- list (stdlib version)
inductive list (A : Type) : Type where
  | nil : list A
  | cons : A → list A → list A

def nil := @list.nil
def cons := @list.cons

-- ============================================================
-- Original.LF_DOT_Basics definitions
-- ============================================================

inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- andb for LF_DOT_Basics
def Original_LF__DOT__Basics_LF_Basics_andb : Original_LF__DOT__Basics_LF_Basics_bool → Original_LF__DOT__Basics_LF_Basics_bool → Original_LF__DOT__Basics_LF_Basics_bool
  | Original_LF__DOT__Basics_LF_Basics_bool.true, b => b
  | Original_LF__DOT__Basics_LF_Basics_bool.false, _ => Original_LF__DOT__Basics_LF_Basics_bool.false

-- plus for LF_DOT_Basics (same as Nat_add but returns nat)
def Original_LF__DOT__Basics_LF_Basics_plus : nat → nat → nat
  | nat.O, m => m
  | nat.S p, m => nat.S (Original_LF__DOT__Basics_LF_Basics_plus p m)

-- eqb for LF_DOT_Basics
def Original_LF__DOT__Basics_LF_Basics_eqb : nat → nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.true
  | nat.S n, nat.S m => Original_LF__DOT__Basics_LF_Basics_eqb n m
  | _, _ => Original_LF__DOT__Basics_LF_Basics_bool.false

-- leb for LF_DOT_Basics
def Original_LF__DOT__Basics_LF_Basics_leb : nat → nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O, _ => Original_LF__DOT__Basics_LF_Basics_bool.true
  | nat.S _, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S n, nat.S m => Original_LF__DOT__Basics_LF_Basics_leb n m

-- ============================================================
-- Original.LF_DOT_Poly definitions (polymorphic list)
-- ============================================================

inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

def Original_LF__DOT__Poly_LF_Poly_cons (X : Type) : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons

def Original_LF__DOT__Poly_LF_Poly_app (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X
  | Original_LF__DOT__Poly_LF_Poly_list.nil, l2 => l2
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t, l2 => Original_LF__DOT__Poly_LF_Poly_list.cons h (Original_LF__DOT__Poly_LF_Poly_app X t l2)

-- ============================================================
-- Original.LF_DOT_Maps definitions
-- ============================================================

def Original_LF__DOT__Maps_LF_Maps_total__map (A : Type) : Type := String_string → A

def Original_LF__DOT__Maps_LF_Maps_t__empty (A : Type) (v : A) : Original_LF__DOT__Maps_LF_Maps_total__map A :=
  fun _ => v

def Original_LF__DOT__Maps_LF_Maps_t__update (A : Type) (m : Original_LF__DOT__Maps_LF_Maps_total__map A)
    (x : String_string) (v : A) : Original_LF__DOT__Maps_LF_Maps_total__map A :=
  fun x' => match String_eqb x x' with
    | Stdlib_bool.true => v
    | Stdlib_bool.false => m x'

-- ============================================================
-- Original.LF_DOT_Imp definitions
-- ============================================================

-- state
def Original_LF__DOT__Imp_LF_Imp_state := Original_LF__DOT__Maps_LF_Maps_total__map nat

-- Character definitions for X, Y, Z
-- 'X' = 88 = 0b01011000, LSB first: 0,0,0,1,1,0,1,0
def charX : Ascii_ascii := Ascii_ascii.Ascii Stdlib_bool.false Stdlib_bool.false Stdlib_bool.false Stdlib_bool.true Stdlib_bool.true Stdlib_bool.false Stdlib_bool.true Stdlib_bool.false
-- 'Y' = 89 = 0b01011001, LSB first: 1,0,0,1,1,0,1,0
def charY : Ascii_ascii := Ascii_ascii.Ascii Stdlib_bool.true Stdlib_bool.false Stdlib_bool.false Stdlib_bool.true Stdlib_bool.true Stdlib_bool.false Stdlib_bool.true Stdlib_bool.false
-- 'Z' = 90 = 0b01011010, LSB first: 0,1,0,1,1,0,1,0
def charZ : Ascii_ascii := Ascii_ascii.Ascii Stdlib_bool.false Stdlib_bool.true Stdlib_bool.false Stdlib_bool.true Stdlib_bool.true Stdlib_bool.false Stdlib_bool.true Stdlib_bool.false

def Original_LF__DOT__Imp_LF_Imp_X : String_string := String_string.String charX String_string.EmptyString
def Original_LF__DOT__Imp_LF_Imp_Y : String_string := String_string.String charY String_string.EmptyString

-- aexp: arithmetic expressions
inductive Original_LF__DOT__Imp_LF_Imp_aexp : Type where
  | ANum : nat → Original_LF__DOT__Imp_LF_Imp_aexp
  | AId : String_string → Original_LF__DOT__Imp_LF_Imp_aexp
  | APlus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp
  | AMinus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp
  | AMult : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp

def Original_LF__DOT__Imp_LF_Imp_ANum := Original_LF__DOT__Imp_LF_Imp_aexp.ANum
def Original_LF__DOT__Imp_LF_Imp_AId := Original_LF__DOT__Imp_LF_Imp_aexp.AId

-- bexp: boolean expressions
inductive Original_LF__DOT__Imp_LF_Imp_bexp : Type where
  | BTrue : Original_LF__DOT__Imp_LF_Imp_bexp
  | BFalse : Original_LF__DOT__Imp_LF_Imp_bexp
  | BEq : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BNeq : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BLe : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BGt : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BNot : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BAnd : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp

-- com: commands
inductive Original_LF__DOT__Imp_LF_Imp_com : Type where
  | CSkip : Original_LF__DOT__Imp_LF_Imp_com
  | CAsgn : String_string → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_com
  | CSeq : Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com
  | CIf : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com
  | CWhile : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com

def Original_LF__DOT__Imp_LF_Imp_CSkip := Original_LF__DOT__Imp_LF_Imp_com.CSkip
def Original_LF__DOT__Imp_LF_Imp_CAsgn := Original_LF__DOT__Imp_LF_Imp_com.CAsgn
def Original_LF__DOT__Imp_LF_Imp_CSeq := Original_LF__DOT__Imp_LF_Imp_com.CSeq
def Original_LF__DOT__Imp_LF_Imp_CIf := Original_LF__DOT__Imp_LF_Imp_com.CIf
def Original_LF__DOT__Imp_LF_Imp_CWhile := Original_LF__DOT__Imp_LF_Imp_com.CWhile

-- aeval
def Original_LF__DOT__Imp_LF_Imp_aeval (st : Original_LF__DOT__Imp_LF_Imp_state) : Original_LF__DOT__Imp_LF_Imp_aexp → nat
  | Original_LF__DOT__Imp_LF_Imp_aexp.ANum n => n
  | Original_LF__DOT__Imp_LF_Imp_aexp.AId x => st x
  | Original_LF__DOT__Imp_LF_Imp_aexp.APlus a1 a2 => Nat_add (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
  | Original_LF__DOT__Imp_LF_Imp_aexp.AMinus a1 a2 => Nat_sub (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
  | Original_LF__DOT__Imp_LF_Imp_aexp.AMult a1 a2 => Nat_mul (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)

-- beval
def Original_LF__DOT__Imp_LF_Imp_beval (st : Original_LF__DOT__Imp_LF_Imp_state) : Original_LF__DOT__Imp_LF_Imp_bexp → Stdlib_bool
  | Original_LF__DOT__Imp_LF_Imp_bexp.BTrue => Stdlib_bool.true
  | Original_LF__DOT__Imp_LF_Imp_bexp.BFalse => Stdlib_bool.false
  | Original_LF__DOT__Imp_LF_Imp_bexp.BEq a1 a2 => Nat_eqb (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
  | Original_LF__DOT__Imp_LF_Imp_bexp.BNeq a1 a2 => negb (Nat_eqb (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2))
  | Original_LF__DOT__Imp_LF_Imp_bexp.BLe a1 a2 => Nat_leb (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
  | Original_LF__DOT__Imp_LF_Imp_bexp.BGt a1 a2 => negb (Nat_leb (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2))
  | Original_LF__DOT__Imp_LF_Imp_bexp.BNot b1 => negb (Original_LF__DOT__Imp_LF_Imp_beval st b1)
  | Original_LF__DOT__Imp_LF_Imp_bexp.BAnd b1 b2 => andb (Original_LF__DOT__Imp_LF_Imp_beval st b1) (Original_LF__DOT__Imp_LF_Imp_beval st b2)

-- empty_st
def Original_LF__DOT__Imp_LF_Imp_empty__st : Original_LF__DOT__Imp_LF_Imp_state :=
  Original_LF__DOT__Maps_LF_Maps_t__empty nat nat.O

-- ============================================================
-- Original.LF_DOT_IndProp definitions (regular expressions)
-- ============================================================

inductive Original_LF__DOT__IndProp_LF_IndProp_reg__exp (T : Type) : Type where
  | EmptySet : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | EmptyStr : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Char : T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | App : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Union : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Star : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T

def Original_LF__DOT__IndProp_LF_IndProp_EmptySet (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptySet

def Original_LF__DOT__IndProp_LF_IndProp_EmptyStr (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptyStr

def Original_LF__DOT__IndProp_LF_IndProp_Char (T : Type) (t : T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Char t

def Original_LF__DOT__IndProp_LF_IndProp_App (T : Type) (r1 r2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.App r1 r2

def Original_LF__DOT__IndProp_LF_IndProp_Union (T : Type) (r1 r2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Union r1 r2

def Original_LF__DOT__IndProp_LF_IndProp_Star (T : Type) (r : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star r

-- exp_match
inductive Original_LF__DOT__IndProp_LF_IndProp_exp__match {T : Type} : Original_LF__DOT__Poly_LF_Poly_list T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Prop where
  | MEmpty : Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_list.nil) (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptyStr)
  | MChar (x : T) : Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_list.cons x Original_LF__DOT__Poly_LF_Poly_list.nil) (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Char x)
  | MApp (s1 : Original_LF__DOT__Poly_LF_Poly_list T) (re1 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) (s2 : Original_LF__DOT__Poly_LF_Poly_list T) (re2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
         (H1 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s1 re1)
         (H2 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s2 re2)
       : Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_app T s1 s2) (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.App re1 re2)
  | MUnionL (s1 : Original_LF__DOT__Poly_LF_Poly_list T) (re1 re2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
            (H1 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s1 re1)
          : Original_LF__DOT__IndProp_LF_IndProp_exp__match s1 (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Union re1 re2)
  | MUnionR (s2 : Original_LF__DOT__Poly_LF_Poly_list T) (re1 re2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
            (H2 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s2 re2)
          : Original_LF__DOT__IndProp_LF_IndProp_exp__match s2 (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Union re1 re2)
  | MStar0 (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_list.nil) (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star re)
  | MStarApp (s1 s2 : Original_LF__DOT__Poly_LF_Poly_list T) (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
             (H1 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s1 re)
             (H2 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s2 (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star re))
           : Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_app T s1 s2) (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star re)

-- ============================================================
-- Original.LF_DOT_ImpParser definitions
-- ============================================================

-- token
def Original_LF__DOT__ImpParser_LF_ImpParser_token : Type := String_string

-- optionE
inductive Original_LF__DOT__ImpParser_LF_ImpParser_optionE (X : Type) : Type where
  | SomeE : X → Original_LF__DOT__ImpParser_LF_ImpParser_optionE X
  | NoneE : String_string → Original_LF__DOT__ImpParser_LF_ImpParser_optionE X

-- ============================================================
-- Original.False (different from Prop False)
-- ============================================================

inductive Original_False : Prop where

-- ============================================================
-- List_In (membership predicate)
-- ============================================================

-- or type for Prop
inductive or (A B : Prop) : Prop where
  | inl : A → or A B
  | inr : B → or A B

-- and type for Prop
inductive and (A B : Prop) : Prop where
  | intro : A → B → and A B

def List_In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | list.nil => MyFalse
  | list.cons x' l' => or (Corelib_Init_Logic_eq x' x) (List_In x l')

-- ============================================================
-- Additional definitions for missing items
-- ============================================================

-- option type
inductive option (A : Type) : Type where
  | None : option A
  | Some : A → option A

def None := @option.None
def Some := @option.Some

-- Subseq inductive
inductive Original_LF__DOT__IndProp_LF_IndProp_subseq {A : Type} : Original_LF__DOT__Poly_LF_Poly_list A → Original_LF__DOT__Poly_LF_Poly_list A → Prop where
  | subseq_nil : Original_LF__DOT__IndProp_LF_IndProp_subseq Original_LF__DOT__Poly_LF_Poly_list.nil Original_LF__DOT__Poly_LF_Poly_list.nil
  | subseq_take : ∀ x l1 l2, Original_LF__DOT__IndProp_LF_IndProp_subseq l1 l2 → 
      Original_LF__DOT__IndProp_LF_IndProp_subseq (Original_LF__DOT__Poly_LF_Poly_list.cons x l1) (Original_LF__DOT__Poly_LF_Poly_list.cons x l2)
  | subseq_skip : ∀ x l1 l2, Original_LF__DOT__IndProp_LF_IndProp_subseq l1 l2 → 
      Original_LF__DOT__IndProp_LF_IndProp_subseq l1 (Original_LF__DOT__Poly_LF_Poly_list.cons x l2)

-- In from IndProp (recall In from Poly) - uses Original Poly list  
def Original_LF__DOT__IndProp_LF_IndProp_In {A : Type} (x : A) : Original_LF__DOT__Poly_LF_Poly_list A → Prop
  | Original_LF__DOT__Poly_LF_Poly_list.nil => MyFalse
  | Original_LF__DOT__Poly_LF_Poly_list.cons x' l' => or (Corelib_Init_Logic_eq x' x) (Original_LF__DOT__IndProp_LF_IndProp_In x l')

-- length function
def Original_LF__DOT__Poly_LF_Poly_length {A : Type} : Original_LF__DOT__Poly_LF_Poly_list A → nat
  | Original_LF__DOT__Poly_LF_Poly_list.nil => nat.O
  | Original_LF__DOT__Poly_LF_Poly_list.cons _ t => nat.S (Original_LF__DOT__Poly_LF_Poly_length t)

-- filter function
def Original_LF__DOT__Poly_LF_Poly_filter {X : Type} (test : X → Original_LF__DOT__Basics_LF_Basics_bool) : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X
  | Original_LF__DOT__Poly_LF_Poly_list.nil => Original_LF__DOT__Poly_LF_Poly_list.nil
  | Original_LF__DOT__Poly_LF_Poly_list.cons x l => match test x with
    | Original_LF__DOT__Basics_LF_Basics_bool.true => Original_LF__DOT__Poly_LF_Poly_list.cons x (Original_LF__DOT__Poly_LF_Poly_filter test l)
    | Original_LF__DOT__Basics_LF_Basics_bool.false => Original_LF__DOT__Poly_LF_Poly_filter test l

-- rev (reverse) function  
def Original_LF__DOT__Poly_LF_Poly_rev (A : Type) : Original_LF__DOT__Poly_LF_Poly_list A → Original_LF__DOT__Poly_LF_Poly_list A
  | Original_LF__DOT__Poly_LF_Poly_list.nil => Original_LF__DOT__Poly_LF_Poly_list.nil
  | Original_LF__DOT__Poly_LF_Poly_list.cons x l => Original_LF__DOT__Poly_LF_Poly_app A (Original_LF__DOT__Poly_LF_Poly_rev A l) (Original_LF__DOT__Poly_LF_Poly_list.cons x Original_LF__DOT__Poly_LF_Poly_list.nil)

-- map function
def Original_LF__DOT__Poly_LF_Poly_map (X Y : Type) (f : X → Y) : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list Y
  | Original_LF__DOT__Poly_LF_Poly_list.nil => Original_LF__DOT__Poly_LF_Poly_list.nil
  | Original_LF__DOT__Poly_LF_Poly_list.cons x l => Original_LF__DOT__Poly_LF_Poly_list.cons (f x) (Original_LF__DOT__Poly_LF_Poly_map X Y f l)

-- odd/even functions
def Original_LF__DOT__Basics_LF_Basics_even : nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O => Original_LF__DOT__Basics_LF_Basics_bool.true
  | nat.S nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S (nat.S n) => Original_LF__DOT__Basics_LF_Basics_even n

def Original_LF__DOT__Basics_LF_Basics_odd : nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S nat.O => Original_LF__DOT__Basics_LF_Basics_bool.true
  | nat.S (nat.S n) => Original_LF__DOT__Basics_LF_Basics_odd n

def Original_LF__DOT__Basics_LF_Basics_negb : Original_LF__DOT__Basics_LF_Basics_bool → Original_LF__DOT__Basics_LF_Basics_bool
  | Original_LF__DOT__Basics_LF_Basics_bool.true => Original_LF__DOT__Basics_LF_Basics_bool.false
  | Original_LF__DOT__Basics_LF_Basics_bool.false => Original_LF__DOT__Basics_LF_Basics_bool.true

-- count for IndProp (counts occurrences of n in list)
def Original_LF__DOT__IndProp_LF_IndProp_count (n : nat) : Original_LF__DOT__Poly_LF_Poly_list nat → nat
  | Original_LF__DOT__Poly_LF_Poly_list.nil => nat.O
  | Original_LF__DOT__Poly_LF_Poly_list.cons x l =>
    match Original_LF__DOT__Basics_LF_Basics_eqb n x with
    | Original_LF__DOT__Basics_LF_Basics_bool.true => nat.S (Original_LF__DOT__IndProp_LF_IndProp_count n l)
    | Original_LF__DOT__Basics_LF_Basics_bool.false => Original_LF__DOT__IndProp_LF_IndProp_count n l

-- In for Logic (membership in list)
def Original_LF__DOT__Logic_LF_Logic_In {A : Type} (x : A) : Original_LF__DOT__Poly_LF_Poly_list A → Prop
  | Original_LF__DOT__Poly_LF_Poly_list.nil => MyFalse
  | Original_LF__DOT__Poly_LF_Poly_list.cons x' l => x' = x ∨ Original_LF__DOT__Logic_LF_Logic_In x l

-- Church numerals type alias (cnat)
def Original_LF__DOT__Poly_LF_Poly_Exercises_cnat : Type 1 := ∀ (X : Type), (X → X) → X → X

-- Church numeral two
def Original_LF__DOT__Poly_LF_Poly_Exercises_two : Original_LF__DOT__Poly_LF_Poly_Exercises_cnat :=
  fun (X : Type) (f : X → X) (x : X) => f (f x)

-- doit3times function
def Original_LF__DOT__Poly_LF_Poly_doit3times {X : Type} (f : X → X) (x : X) : X := f (f (f x))

-- countoddmembers' (count odd members)
def Original_LF__DOT__Poly_LF_Poly_countoddmembers' : Original_LF__DOT__Poly_LF_Poly_list nat → nat :=
  fun l => Original_LF__DOT__Poly_LF_Poly_length (Original_LF__DOT__Poly_LF_Poly_filter Original_LF__DOT__Basics_LF_Basics_odd l)

-- partial_map
def Original_LF__DOT__Maps_LF_Maps_partial__map (A : Type) : Type :=
  Original_LF__DOT__Maps_LF_Maps_total__map (option A)

-- update for partial maps (uses option)
def Original_LF__DOT__Maps_LF_Maps_update {A : Type} (m : Original_LF__DOT__Maps_LF_Maps_partial__map A) (x : String_string) (v : A) : Original_LF__DOT__Maps_LF_Maps_partial__map A :=
  Original_LF__DOT__Maps_LF_Maps_t__update (option A) m x (option.Some v)

-- ============================================================
-- Theorems (admitted in Original.v - using sorry)
-- ============================================================

-- add_assoc_from_induction : associativity of addition
axiom Original_LF__DOT__AltAuto_LF_AltAuto_add__assoc__from__induction :
  ∀ n m p : nat, Corelib_Init_Logic_eq (Nat_add n (Nat_add m p)) (Nat_add (Nat_add n m) p)

-- imp2: P -> (P -> Q) -> Q
axiom Original_LF__DOT__AltAuto_LF_AltAuto_imp2 :
  ∀ P Q : Prop, P → (P → Q) → Q

-- intuition_succeed2: ~ (P \/ Q) -> ~P /\ ~Q
axiom Original_LF__DOT__AltAuto_LF_AltAuto_intuition__succeed2 :
  ∀ P Q : Prop, (or P Q → MyFalse) → and (P → MyFalse) (Q → MyFalse)

-- not_true_is_false
axiom Original_LF__DOT__Logic_LF_Logic_not__true__is__false :
  ∀ b : Original_LF__DOT__Basics_LF_Basics_bool,
    Logic_not (Corelib_Init_Logic_eq b Original_LF__DOT__Basics_LF_Basics_bool.true) →
    Corelib_Init_Logic_eq b Original_LF__DOT__Basics_LF_Basics_bool.false

-- update_shadow for maps
axiom Original_LF__DOT__Maps_LF_Maps_update__shadow :
  ∀ (A : Type) (m : Original_LF__DOT__Maps_LF_Maps_partial__map A) x v1 v2,
    Corelib_Init_Logic_eq
      (Original_LF__DOT__Maps_LF_Maps_update (Original_LF__DOT__Maps_LF_Maps_update m x v1) x v2)
      (Original_LF__DOT__Maps_LF_Maps_update m x v2)

-- test_countoddmembers'3
axiom Original_LF__DOT__Poly_LF_Poly_test__countoddmembers'3 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Poly_LF_Poly_countoddmembers'
      (Original_LF__DOT__Poly_LF_Poly_list.cons (nat.S (nat.S (nat.S (nat.S nat.O))))
        (Original_LF__DOT__Poly_LF_Poly_list.cons (nat.S nat.O)
          (Original_LF__DOT__Poly_LF_Poly_list.cons (nat.S (nat.S nat.O))
            (Original_LF__DOT__Poly_LF_Poly_list.cons (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))
              Original_LF__DOT__Poly_LF_Poly_list.nil)))))
    (nat.S (nat.S (nat.S nat.O)))

-- test_rev1
axiom Original_LF__DOT__Poly_LF_Poly_test__rev1 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Poly_LF_Poly_rev nat
      (Original_LF__DOT__Poly_LF_Poly_list.cons (nat.S nat.O)
        (Original_LF__DOT__Poly_LF_Poly_list.cons (nat.S (nat.S nat.O))
          (Original_LF__DOT__Poly_LF_Poly_list.cons (nat.S (nat.S (nat.S nat.O)))
            Original_LF__DOT__Poly_LF_Poly_list.nil))))
    (Original_LF__DOT__Poly_LF_Poly_list.cons (nat.S (nat.S (nat.S nat.O)))
      (Original_LF__DOT__Poly_LF_Poly_list.cons (nat.S (nat.S nat.O))
        (Original_LF__DOT__Poly_LF_Poly_list.cons (nat.S nat.O) Original_LF__DOT__Poly_LF_Poly_list.nil)))

-- silly3 from Tactics
axiom Original_LF__DOT__Tactics_LF_Tactics_silly3 :
  ∀ n : nat, Stdlib_bool.true = Nat_eqb n (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))) →
    Stdlib_bool.true = Nat_eqb (nat.S (nat.S n)) (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))))

-- subseq_trans (transitive subseq)
axiom Original_LF__DOT__IndProp_LF_IndProp_subseq__trans :
  ∀ (l1 l2 l3 : Original_LF__DOT__Poly_LF_Poly_list nat),
    Original_LF__DOT__IndProp_LF_IndProp_subseq l1 l2 →
    Original_LF__DOT__IndProp_LF_IndProp_subseq l2 l3 →
    Original_LF__DOT__IndProp_LF_IndProp_subseq l1 l3

-- In recall
axiom Original_LF__DOT__IndProp_LF_IndProp_recall__In__In :
  ∀ (A : Type) (x : A) (l : Original_LF__DOT__Poly_LF_Poly_list A), Original_LF__DOT__IndProp_LF_IndProp_In x l = Original_LF__DOT__IndProp_LF_IndProp_In x l

-- manual_grade_for_XtimesYinZ_spec (Imp) - It's actually a Definition returning option (nat*string) = None
def Original_LF__DOT__Imp_LF_Imp_manual__grade__for__XtimesYinZ__spec : option (prod nat String_string) := option.None

-- ============================================================
-- Rel definitions for next_nat_closure_is_le
-- ============================================================

-- le (less than or equal)
inductive le : nat → nat → Prop where
  | le_n (n : nat) : le n n
  | le_S (n m : nat) : le n m → le n (nat.S m)

-- relation type alias
def Original_LF_Rel_relation (X : Type) : Type := X → X → Prop

-- partial_function
def Original_LF_Rel_partial__function {X : Type} (R : Original_LF_Rel_relation X) : Prop :=
  ∀ x y1 y2 : X, R x y1 → R x y2 → @Corelib_Init_Logic_eq X y1 y2

-- reflexive
def Original_LF_Rel_reflexive {X : Type} (R : Original_LF_Rel_relation X) : Prop :=
  ∀ a : X, R a a

-- transitive
def Original_LF_Rel_transitive {X : Type} (R : Original_LF_Rel_relation X) : Prop :=
  ∀ a b c : X, R a b → R b c → R a c

-- symmetric
def Original_LF_Rel_symmetric {X : Type} (R : Original_LF_Rel_relation X) : Prop :=
  ∀ a b : X, R a b → R b a

-- antisymmetric  
def Original_LF_Rel_antisymmetric {X : Type} (R : Original_LF_Rel_relation X) : Prop :=
  ∀ a b : X, R a b → R b a → @Corelib_Init_Logic_eq X a b

-- preorder
def Original_LF_Rel_preorder {X : Type} (R : Original_LF_Rel_relation X) : Prop :=
  Original_LF_Rel_reflexive R ∧ Original_LF_Rel_transitive R

-- order
def Original_LF_Rel_order {X : Type} (R : Original_LF_Rel_relation X) : Prop :=
  Original_LF_Rel_reflexive R ∧ Original_LF_Rel_antisymmetric R ∧ Original_LF_Rel_transitive R

-- equivalence
def Original_LF_Rel_equivalence {X : Type} (R : Original_LF_Rel_relation X) : Prop :=
  Original_LF_Rel_reflexive R ∧ Original_LF_Rel_symmetric R ∧ Original_LF_Rel_transitive R

-- empty_relation
inductive Original_LF_Rel_empty__relation : nat → nat → Prop where

-- total_relation  
inductive Original_LF_Rel_total__relation : nat → nat → Prop where
  | tot : ∀ n m : nat, Original_LF_Rel_total__relation n m

-- next_nat relation
inductive Original_LF_Rel_next__nat : nat → nat → Prop where
  | nn (n : nat) : Original_LF_Rel_next__nat n (nat.S n)

-- clos_refl_trans (reflexive transitive closure)
inductive Original_LF_Rel_clos__refl__trans {X : Type} (R : X → X → Prop) : X → X → Prop where
  | rt_step (x y : X) : R x y → Original_LF_Rel_clos__refl__trans R x y
  | rt_refl (x : X) : Original_LF_Rel_clos__refl__trans R x x
  | rt_trans (x y z : X) : Original_LF_Rel_clos__refl__trans R x y → Original_LF_Rel_clos__refl__trans R y z → Original_LF_Rel_clos__refl__trans R x z

-- clos_refl_trans_1n (alternative definition)
inductive Original_LF_Rel_clos__refl__trans__1n {A : Type} (R : A → A → Prop) : A → A → Prop where
  | rt1n_refl (x : A) : Original_LF_Rel_clos__refl__trans__1n R x x
  | rt1n_trans (x y z : A) : R x y → Original_LF_Rel_clos__refl__trans__1n R y z → Original_LF_Rel_clos__refl__trans__1n R x z

-- Admitted theorems about relations
axiom Original_LF_Rel_empty__relation__partial__function :
  @Original_LF_Rel_partial__function nat Original_LF_Rel_empty__relation

axiom Original_LF_Rel_total__relation__not__partial__function :
  Logic_not (@Original_LF_Rel_partial__function nat Original_LF_Rel_total__relation)

axiom Original_LF_Rel_next__nat__partial__function :
  @Original_LF_Rel_partial__function nat Original_LF_Rel_next__nat

axiom Original_LF_Rel_le__not__a__partial__function :
  Logic_not (@Original_LF_Rel_partial__function nat le)

axiom Original_LF_Rel_le__reflexive :
  @Original_LF_Rel_reflexive nat le

axiom Original_LF_Rel_le__trans :
  @Original_LF_Rel_transitive nat le

axiom Original_LF_Rel_le__antisymmetric :
  @Original_LF_Rel_antisymmetric nat le

axiom Original_LF_Rel_le__not__symmetric :
  Logic_not (@Original_LF_Rel_symmetric nat le)

axiom Original_LF_Rel_le__order :
  @Original_LF_Rel_order nat le

axiom Original_LF_Rel_rsc__R :
  ∀ (X : Type) (R : X → X → Prop) (x y : X),
    R x y → Original_LF_Rel_clos__refl__trans__1n R x y

axiom Original_LF_Rel_rsc__trans :
  ∀ (X : Type) (R : X → X → Prop) (x y z : X),
    Original_LF_Rel_clos__refl__trans__1n R x y →
    Original_LF_Rel_clos__refl__trans__1n R y z →
    Original_LF_Rel_clos__refl__trans__1n R x z

axiom Original_LF_Rel_rtc__rsc__coincide :
  ∀ (X : Type) (R : X → X → Prop) (x y : X),
    Original_LF_Rel_clos__refl__trans R x y ↔ Original_LF_Rel_clos__refl__trans__1n R x y

-- le_S_n : S n <= S m -> n <= m
axiom Original_LF_Rel_le__S__n :
  ∀ n m : nat, le (nat.S n) (nat.S m) → le n m

axiom Original_LF_Rel_le__Sn__n :
  ∀ n : nat, Logic_not (le (nat.S n) n)

axiom Original_LF_Rel_le__Sn__le :
  ∀ n m : nat, le (nat.S n) m → le n m

axiom Original_LF_Rel_le__step :
  ∀ n m p : nat, le n m → le m (nat.S p) → le n p

-- ============================================================
-- BreakImp definitions
-- ============================================================

-- result type
inductive Original_LF__DOT__Imp_LF_Imp_BreakImp_result : Type where
  | SContinue : Original_LF__DOT__Imp_LF_Imp_BreakImp_result
  | SBreak : Original_LF__DOT__Imp_LF_Imp_BreakImp_result

def Original_LF__DOT__Imp_LF_Imp_BreakImp_SContinue := Original_LF__DOT__Imp_LF_Imp_BreakImp_result.SContinue
def Original_LF__DOT__Imp_LF_Imp_BreakImp_SBreak := Original_LF__DOT__Imp_LF_Imp_BreakImp_result.SBreak

-- BreakImp command type
inductive Original_LF__DOT__Imp_LF_Imp_BreakImp_com : Type where
  | CSkip : Original_LF__DOT__Imp_LF_Imp_BreakImp_com
  | CBreak : Original_LF__DOT__Imp_LF_Imp_BreakImp_com
  | CAsgn : String_string → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_BreakImp_com
  | CSeq : Original_LF__DOT__Imp_LF_Imp_BreakImp_com → Original_LF__DOT__Imp_LF_Imp_BreakImp_com → Original_LF__DOT__Imp_LF_Imp_BreakImp_com
  | CIf : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_BreakImp_com → Original_LF__DOT__Imp_LF_Imp_BreakImp_com → Original_LF__DOT__Imp_LF_Imp_BreakImp_com
  | CWhile : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_BreakImp_com → Original_LF__DOT__Imp_LF_Imp_BreakImp_com

def Original_LF__DOT__Imp_LF_Imp_BreakImp_CSeq := Original_LF__DOT__Imp_LF_Imp_BreakImp_com.CSeq

-- ceval for BreakImp (big-step semantics)
inductive Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval :
  Original_LF__DOT__Imp_LF_Imp_BreakImp_com →
  Original_LF__DOT__Imp_LF_Imp_state →
  Original_LF__DOT__Imp_LF_Imp_BreakImp_result →
  Original_LF__DOT__Imp_LF_Imp_state → Prop where
  | E_Skip : ∀ (st : Original_LF__DOT__Imp_LF_Imp_state),
      Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval
        Original_LF__DOT__Imp_LF_Imp_BreakImp_com.CSkip
        st
        Original_LF__DOT__Imp_LF_Imp_BreakImp_result.SContinue
        st
  | E_Break : ∀ (st : Original_LF__DOT__Imp_LF_Imp_state),
      Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval
        Original_LF__DOT__Imp_LF_Imp_BreakImp_com.CBreak
        st
        Original_LF__DOT__Imp_LF_Imp_BreakImp_result.SBreak
        st
  | E_Asgn : ∀ (st : Original_LF__DOT__Imp_LF_Imp_state) (a : Original_LF__DOT__Imp_LF_Imp_aexp) (x : String_string),
      Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval
        (Original_LF__DOT__Imp_LF_Imp_BreakImp_com.CAsgn x a)
        st
        Original_LF__DOT__Imp_LF_Imp_BreakImp_result.SContinue
        (Original_LF__DOT__Maps_LF_Maps_t__update nat st x (Original_LF__DOT__Imp_LF_Imp_aeval st a))
  | E_SeqContinue : ∀ (c1 c2 : Original_LF__DOT__Imp_LF_Imp_BreakImp_com)
      (st st' st'' : Original_LF__DOT__Imp_LF_Imp_state) (r : Original_LF__DOT__Imp_LF_Imp_BreakImp_result),
      Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval c1 st Original_LF__DOT__Imp_LF_Imp_BreakImp_result.SContinue st' →
      Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval c2 st' r st'' →
      Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval
        (Original_LF__DOT__Imp_LF_Imp_BreakImp_com.CSeq c1 c2)
        st r st''
  | E_SeqBreak : ∀ (c1 c2 : Original_LF__DOT__Imp_LF_Imp_BreakImp_com)
      (st st' : Original_LF__DOT__Imp_LF_Imp_state),
      Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval c1 st Original_LF__DOT__Imp_LF_Imp_BreakImp_result.SBreak st' →
      Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval
        (Original_LF__DOT__Imp_LF_Imp_BreakImp_com.CSeq c1 c2)
        st Original_LF__DOT__Imp_LF_Imp_BreakImp_result.SBreak st'
  | E_IfTrue : ∀ (st st' : Original_LF__DOT__Imp_LF_Imp_state) (r : Original_LF__DOT__Imp_LF_Imp_BreakImp_result)
      (b : Original_LF__DOT__Imp_LF_Imp_bexp) (c1 c2 : Original_LF__DOT__Imp_LF_Imp_BreakImp_com),
      Original_LF__DOT__Imp_LF_Imp_beval st b = Stdlib_bool.true →
      Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval c1 st r st' →
      Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval
        (Original_LF__DOT__Imp_LF_Imp_BreakImp_com.CIf b c1 c2)
        st r st'
  | E_IfFalse : ∀ (st st' : Original_LF__DOT__Imp_LF_Imp_state) (r : Original_LF__DOT__Imp_LF_Imp_BreakImp_result)
      (b : Original_LF__DOT__Imp_LF_Imp_bexp) (c1 c2 : Original_LF__DOT__Imp_LF_Imp_BreakImp_com),
      Original_LF__DOT__Imp_LF_Imp_beval st b = Stdlib_bool.false →
      Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval c2 st r st' →
      Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval
        (Original_LF__DOT__Imp_LF_Imp_BreakImp_com.CIf b c1 c2)
        st r st'
  | E_WhileFalse : ∀ (st : Original_LF__DOT__Imp_LF_Imp_state)
      (b : Original_LF__DOT__Imp_LF_Imp_bexp) (c : Original_LF__DOT__Imp_LF_Imp_BreakImp_com),
      Original_LF__DOT__Imp_LF_Imp_beval st b = Stdlib_bool.false →
      Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval
        (Original_LF__DOT__Imp_LF_Imp_BreakImp_com.CWhile b c)
        st Original_LF__DOT__Imp_LF_Imp_BreakImp_result.SContinue st
  | E_WhileTrueBreak : ∀ (st st' : Original_LF__DOT__Imp_LF_Imp_state)
      (b : Original_LF__DOT__Imp_LF_Imp_bexp) (c : Original_LF__DOT__Imp_LF_Imp_BreakImp_com),
      Original_LF__DOT__Imp_LF_Imp_beval st b = Stdlib_bool.true →
      Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval c st Original_LF__DOT__Imp_LF_Imp_BreakImp_result.SBreak st' →
      Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval
        (Original_LF__DOT__Imp_LF_Imp_BreakImp_com.CWhile b c)
        st Original_LF__DOT__Imp_LF_Imp_BreakImp_result.SContinue st'
  | E_WhileTrueContinue : ∀ (st st' st'' : Original_LF__DOT__Imp_LF_Imp_state) (r : Original_LF__DOT__Imp_LF_Imp_BreakImp_result)
      (b : Original_LF__DOT__Imp_LF_Imp_bexp) (c : Original_LF__DOT__Imp_LF_Imp_BreakImp_com),
      Original_LF__DOT__Imp_LF_Imp_beval st b = Stdlib_bool.true →
      Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval c st Original_LF__DOT__Imp_LF_Imp_BreakImp_result.SContinue st' →
      Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval (Original_LF__DOT__Imp_LF_Imp_BreakImp_com.CWhile b c) st' r st'' →
      Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval
        (Original_LF__DOT__Imp_LF_Imp_BreakImp_com.CWhile b c)
        st r st''

-- ============================================================
-- Admitted theorems
-- ============================================================

-- next_nat_closure_is_le: Admitted in Original.v
axiom Original_LF_Rel_next__nat__closure__is__le :
  ∀ (x x0 : nat), iff (le x x0) (Original_LF_Rel_clos__refl__trans (fun (H H0 : nat) => Original_LF_Rel_next__nat H H0) x x0)

-- andb_true_elim2: Admitted in Original.v
axiom Original_LF__DOT__Basics_LF_Basics_andb__true__elim2 :
  ∀ (b c : Original_LF__DOT__Basics_LF_Basics_bool),
    Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_andb b c) Original_LF__DOT__Basics_LF_Basics_true →
    Corelib_Init_Logic_eq c Original_LF__DOT__Basics_LF_Basics_true

-- seq_stops_on_break: Admitted in Original.v
axiom Original_LF__DOT__Imp_LF_Imp_BreakImp_seq__stops__on__break :
  ∀ (c1 c2 : Original_LF__DOT__Imp_LF_Imp_BreakImp_com)
    (st st' : Original_LF__DOT__Imp_LF_Imp_state),
    Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval c1 st Original_LF__DOT__Imp_LF_Imp_BreakImp_result.SBreak st' →
    Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval
      (Original_LF__DOT__Imp_LF_Imp_BreakImp_com.CSeq c1 c2)
      st
      Original_LF__DOT__Imp_LF_Imp_BreakImp_result.SBreak
      st'

-- add_comm': Admitted in Original.v
axiom Original_LF__DOT__IndPrinciples_LF_IndPrinciples_add__comm' :
  ∀ (n m : nat), Corelib_Init_Logic_eq (Nat_add n m) (Nat_add m n)

-- plus_one_r': Admitted in Original.v
axiom Original_LF__DOT__IndPrinciples_LF_IndPrinciples_plus__one__r' :
  ∀ (n : nat), Corelib_Init_Logic_eq (Nat_add n (nat.S nat.O)) (nat.S n)

-- eqbP_practice: Admitted in Original.v
axiom Original_LF__DOT__IndProp_LF_IndProp_eqbP__practice :
  ∀ (n : nat) (l : Original_LF__DOT__Poly_LF_Poly_list nat),
    Corelib_Init_Logic_eq (Original_LF__DOT__IndProp_LF_IndProp_count n l) nat.O →
    Original_LF__DOT__Logic_LF_Logic_In n l → MyFalse

-- contrapositive: Admitted in Original.v
axiom Original_LF__DOT__Logic_LF_Logic_contrapositive :
  ∀ (P Q : Prop), (P → Q) → (Logic_not Q → Logic_not P)

-- or_intro_l: Admitted in Original.v
axiom Original_LF__DOT__Logic_LF_Logic_or__intro__l :
  ∀ (A B : Prop), A → or A B

-- two_church_peano: Admitted in Original.v
axiom Original_LF__DOT__Poly_LF_Poly_Exercises_two__church__peano :
  ∀ (X : Type) (f : X → X) (x : X),
    Corelib_Init_Logic_eq (Original_LF__DOT__Poly_LF_Poly_Exercises_two X f x) (f (f x))

-- rev_app_distr: Admitted in Original.v
axiom Original_LF__DOT__Poly_LF_Poly_rev__app__distr :
  ∀ (X : Type) (l1 l2 : Original_LF__DOT__Poly_LF_Poly_list X),
    @Corelib_Init_Logic_eq (Original_LF__DOT__Poly_LF_Poly_list X)
      (Original_LF__DOT__Poly_LF_Poly_rev X (Original_LF__DOT__Poly_LF_Poly_app X l1 l2))
      (Original_LF__DOT__Poly_LF_Poly_app X (Original_LF__DOT__Poly_LF_Poly_rev X l2) (Original_LF__DOT__Poly_LF_Poly_rev X l1))

-- test_anon_fun': Admitted in Original.v  
axiom Original_LF__DOT__Poly_LF_Poly_test__anon__fun' :
  @Corelib_Init_Logic_eq (Original_LF__DOT__Poly_LF_Poly_list nat)
    (Original_LF__DOT__Poly_LF_Poly_map nat nat (fun x => Original_LF__DOT__Basics_LF_Basics_plus (nat.S (nat.S (nat.S nat.O))) x)
       (Original_LF__DOT__Poly_LF_Poly_cons nat (nat.S (nat.S nat.O))
          (Original_LF__DOT__Poly_LF_Poly_cons nat nat.O
             (Original_LF__DOT__Poly_LF_Poly_cons nat (nat.S (nat.S nat.O)) (Original_LF__DOT__Poly_LF_Poly_nil nat)))))
    (Original_LF__DOT__Poly_LF_Poly_cons nat (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))
       (Original_LF__DOT__Poly_LF_Poly_cons nat (nat.S (nat.S (nat.S nat.O)))
          (Original_LF__DOT__Poly_LF_Poly_cons nat (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))) (Original_LF__DOT__Poly_LF_Poly_nil nat))))

-- test_map1: Admitted in Original.v
axiom Original_LF__DOT__Poly_LF_Poly_test__map1 :
  @Corelib_Init_Logic_eq (Original_LF__DOT__Poly_LF_Poly_list nat)
    (Original_LF__DOT__Poly_LF_Poly_map nat nat (fun x => Original_LF__DOT__Basics_LF_Basics_plus (nat.S (nat.S (nat.S nat.O))) x)
       (Original_LF__DOT__Poly_LF_Poly_cons nat (nat.S (nat.S nat.O))
          (Original_LF__DOT__Poly_LF_Poly_cons nat nat.O
             (Original_LF__DOT__Poly_LF_Poly_cons nat (nat.S (nat.S nat.O)) (Original_LF__DOT__Poly_LF_Poly_nil nat)))))
    (Original_LF__DOT__Poly_LF_Poly_cons nat (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))
       (Original_LF__DOT__Poly_LF_Poly_cons nat (nat.S (nat.S (nat.S nat.O)))
          (Original_LF__DOT__Poly_LF_Poly_cons nat (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))) (Original_LF__DOT__Poly_LF_Poly_nil nat))))

-- ============================================================
-- Admitted theorems needed for main checker files
-- ============================================================

-- test_leb2: Admitted in Original.v
axiom Original_LF__DOT__Basics_LF_Basics_test__leb2 :
  @Corelib_Init_Logic_eq Original_LF__DOT__Basics_LF_Basics_bool
    (Original_LF__DOT__Basics_LF_Basics_leb (nat.S (nat.S nat.O)) (nat.S (nat.S (nat.S (nat.S nat.O)))))
    Original_LF__DOT__Basics_LF_Basics_bool.true

-- zero_nbeq_plus_1: Admitted in Original.v
axiom Original_LF__DOT__Basics_LF_Basics_zero__nbeq__plus__1 : ∀ (n : nat),
  @Corelib_Init_Logic_eq Original_LF__DOT__Basics_LF_Basics_bool
    (Original_LF__DOT__Basics_LF_Basics_eqb nat.O (Nat_add n (nat.S nat.O)))
    Original_LF__DOT__Basics_LF_Basics_bool.false

-- leb_complete: Admitted in Original.v
axiom Original_LF__DOT__IndProp_LF_IndProp_leb__complete : ∀ (n m : nat),
  @Corelib_Init_Logic_eq Original_LF__DOT__Basics_LF_Basics_bool
    (Original_LF__DOT__Basics_LF_Basics_leb n m)
    Original_LF__DOT__Basics_LF_Basics_bool.true →
  @le n m

-- leb_iff: Admitted in Original.v
axiom Original_LF__DOT__IndProp_LF_IndProp_leb__iff : ∀ (n m : nat),
  @iff
    (@Corelib_Init_Logic_eq Original_LF__DOT__Basics_LF_Basics_bool
       (Original_LF__DOT__Basics_LF_Basics_leb n m)
       Original_LF__DOT__Basics_LF_Basics_bool.true)
    (@le n m)

-- eqb_eq: Admitted in Original.v
axiom Original_LF__DOT__Logic_LF_Logic_eqb__eq : ∀ (n m : nat),
  @iff
    (@Corelib_Init_Logic_eq Original_LF__DOT__Basics_LF_Basics_bool
       (Original_LF__DOT__Basics_LF_Basics_eqb n m)
       Original_LF__DOT__Basics_LF_Basics_bool.true)
    (@Corelib_Init_Logic_eq nat n m)

-- plus_eqb_example: Admitted in Original.v
axiom Original_LF__DOT__Logic_LF_Logic_plus__eqb__example : ∀ (n m p : nat),
  @Corelib_Init_Logic_eq Original_LF__DOT__Basics_LF_Basics_bool
    (Original_LF__DOT__Basics_LF_Basics_eqb n m)
    Original_LF__DOT__Basics_LF_Basics_bool.true →
  @Corelib_Init_Logic_eq Original_LF__DOT__Basics_LF_Basics_bool
    (Original_LF__DOT__Basics_LF_Basics_eqb (Nat_add n p) (Nat_add m p))
    Original_LF__DOT__Basics_LF_Basics_bool.true

