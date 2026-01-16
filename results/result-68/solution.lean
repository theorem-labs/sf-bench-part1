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

-- Custom nat
inductive nat : Type where
  | O : nat
  | S : nat → nat

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

-- Predecessor on nat
def Nat_pred : nat → nat
  | nat.O => nat.O
  | nat.S n => n

-- Multiplication on nat
def Nat_mul : nat → nat → nat
  | nat.O, _ => nat.O
  | nat.S n, m => Nat_add m (Nat_mul n m)

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

-- List.In predicate
def List_In {A : Type} (a : A) : list A → Prop
  | list.nil => MyFalse
  | list.cons x xs => a = x ∨ List_In a xs

-- stdlib option
inductive option (A : Type) : Type where
  | None : option A
  | Some : A → option A

def None := @option.None
def Some := @option.Some

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
-- Original.True
-- ============================================================

inductive Original_True : Prop where
  | I : Original_True

-- ============================================================
-- Additional definitions for isomorphisms
-- ============================================================

-- Original.LF_DOT_Basics.LF.Basics.plus
def Original_LF__DOT__Basics_LF_Basics_plus : nat → nat → nat
  | nat.O, m => m
  | nat.S n', m => nat.S (Original_LF__DOT__Basics_LF_Basics_plus n' m)

-- Original.LF_DOT_Poly.LF.Poly.map
def Original_LF__DOT__Poly_LF_Poly_map {X Y : Type} (f : X → Y) : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list Y
  | Original_LF__DOT__Poly_LF_Poly_list.nil => Original_LF__DOT__Poly_LF_Poly_list.nil
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t => Original_LF__DOT__Poly_LF_Poly_list.cons (f h) (Original_LF__DOT__Poly_LF_Poly_map f t)

-- Original.LF_DOT_Logic.LF.Logic.disc_fn (discriminating function)
def Original_LF__DOT__Logic_LF_Logic_disc__fn (n : nat) : Prop :=
  match n with
  | nat.O => Original_True
  | nat.S _ => Original_False

-- Original.LF_DOT_AltAuto.LF.AltAuto.silly2
def Original_LF__DOT__AltAuto_LF_AltAuto_silly2 (P : Prop) (hp : P) : P := hp

-- Original.LF_DOT_Poly.LF.Poly.option
inductive Original_LF__DOT__Poly_LF_Poly_option (X : Type) : Type where
  | Some : X → Original_LF__DOT__Poly_LF_Poly_option X
  | None : Original_LF__DOT__Poly_LF_Poly_option X

def Original_LF__DOT__Poly_LF_Poly_None (X : Type) : Original_LF__DOT__Poly_LF_Poly_option X :=
  Original_LF__DOT__Poly_LF_Poly_option.None

-- Original.LF_DOT_Poly.LF.Poly.prod
inductive Original_LF__DOT__Poly_LF_Poly_prod (X Y : Type) : Type where
  | pair : X → Y → Original_LF__DOT__Poly_LF_Poly_prod X Y

def Original_LF__DOT__Poly_LF_Poly_pair (X Y : Type) (x : X) (y : Y) : Original_LF__DOT__Poly_LF_Poly_prod X Y :=
  Original_LF__DOT__Poly_LF_Poly_prod.pair x y



-- Arithmetic expressions (for Imp)
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

-- optimize_0plus: removes additions of 0 from the left
def Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus : Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp
  | Original_LF__DOT__Imp_LF_Imp_AExp_aexp.ANum n => Original_LF__DOT__Imp_LF_Imp_AExp_aexp.ANum n
  | Original_LF__DOT__Imp_LF_Imp_AExp_aexp.APlus (Original_LF__DOT__Imp_LF_Imp_AExp_aexp.ANum nat.O) e2 => Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus e2
  | Original_LF__DOT__Imp_LF_Imp_AExp_aexp.APlus e1 e2 => Original_LF__DOT__Imp_LF_Imp_AExp_aexp.APlus (Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus e1) (Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus e2)
  | Original_LF__DOT__Imp_LF_Imp_AExp_aexp.AMinus e1 e2 => Original_LF__DOT__Imp_LF_Imp_AExp_aexp.AMinus (Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus e1) (Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus e2)
  | Original_LF__DOT__Imp_LF_Imp_AExp_aexp.AMult e1 e2 => Original_LF__DOT__Imp_LF_Imp_AExp_aexp.AMult (Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus e1) (Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus e2)

-- The soundness theorem (admitted in Original.v, so we use an axiom)
axiom Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__sound : ∀ (a : Original_LF__DOT__Imp_LF_Imp_AExp_aexp),
  Corelib_Init_Logic_eq (Original_LF__DOT__Imp_LF_Imp_AExp_aeval (Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus a)) (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a)

-- test_map1': map (plus 3) [2;0;2] = [5;3;5] (admitted in Original.v)
axiom Original_LF__DOT__Poly_LF_Poly_Exercises_test__map1' :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Poly_LF_Poly_map (fun x => Original_LF__DOT__Basics_LF_Basics_plus (nat.S (nat.S (nat.S nat.O))) x)
       (Original_LF__DOT__Poly_LF_Poly_list.cons (nat.S (nat.S nat.O))
          (Original_LF__DOT__Poly_LF_Poly_list.cons nat.O
             (Original_LF__DOT__Poly_LF_Poly_list.cons (nat.S (nat.S nat.O)) (Original_LF__DOT__Poly_LF_Poly_list.nil)))))
    (Original_LF__DOT__Poly_LF_Poly_list.cons (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))
       (Original_LF__DOT__Poly_LF_Poly_list.cons (nat.S (nat.S (nat.S nat.O)))
          (Original_LF__DOT__Poly_LF_Poly_list.cons (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))) (Original_LF__DOT__Poly_LF_Poly_list.nil))))

-- app_assoc theorem (needs to be proved or admitted)
axiom Original_LF__DOT__Poly_LF_Poly_app__assoc : ∀ (X : Type) (l1 l2 l3 : Original_LF__DOT__Poly_LF_Poly_list X),
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Poly_LF_Poly_app X l1 (Original_LF__DOT__Poly_LF_Poly_app X l2 l3))
    (Original_LF__DOT__Poly_LF_Poly_app X (Original_LF__DOT__Poly_LF_Poly_app X l1 l2) l3)

-- String is list of ascii
def Original_LF__DOT__IndProp_LF_IndProp_string : Type := Original_LF__DOT__Poly_LF_Poly_list Ascii_ascii

-- manual_grade_for_nor_intuition is None
def Original_LF__DOT__AltAuto_LF_AltAuto_manual__grade__for__nor__intuition :
    Original_LF__DOT__Poly_LF_Poly_option (Original_LF__DOT__Poly_LF_Poly_prod nat (Original_LF__DOT__Poly_LF_Poly_list Ascii_ascii)) :=
  Original_LF__DOT__Poly_LF_Poly_option.None

-- t_tree
inductive Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree (X : Type) : Type where
  | t_leaf : Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree X
  | t_branch : Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree X → X →
               Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree X →
               Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree X

-- reflect function
def Original_LF__DOT__IndPrinciples_LF_IndPrinciples_reflect (X : Type)
    (t : Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree X) :
    Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree X :=
  match t with
  | .t_leaf => .t_leaf
  | .t_branch l v r => .t_branch (Original_LF__DOT__IndPrinciples_LF_IndPrinciples_reflect X r) v
                                 (Original_LF__DOT__IndPrinciples_LF_IndPrinciples_reflect X l)

-- reflect_involution (admitted in Original.v)
axiom Original_LF__DOT__IndPrinciples_LF_IndPrinciples_reflect__involution :
  ∀ (X : Type) (t : Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree X),
    Corelib_Init_Logic_eq
      (Original_LF__DOT__IndPrinciples_LF_IndPrinciples_reflect X
        (Original_LF__DOT__IndPrinciples_LF_IndPrinciples_reflect X t))
      t

-- eq_example2 (admitted in Original.v)
axiom Original_LF__DOT__AltAuto_LF_AltAuto_eq__example2 :
  ∀ (n m o p : nat),
    Corelib_Init_Logic_eq n m →
    Corelib_Init_Logic_eq o p →
    Corelib_Init_Logic_eq (Original_LF__DOT__Poly_LF_Poly_pair nat nat n o) (Original_LF__DOT__Poly_LF_Poly_pair nat nat m p)

-- manual_grade_for_re_opt = None : option (nat * IndProp.string)
def Original_LF__DOT__AltAuto_LF_AltAuto_manual__grade__for__re__opt : 
    Original_LF__DOT__Poly_LF_Poly_option 
      (Original_LF__DOT__Poly_LF_Poly_prod nat Original_LF__DOT__IndProp_LF_IndProp_string) :=
  Original_LF__DOT__Poly_LF_Poly_option.None

-- aevalR relation (main version)
inductive Original_LF__DOT__Imp_LF_Imp_AExp_aevalR : Original_LF__DOT__Imp_LF_Imp_AExp_aexp → nat → Prop where
  | E_ANum (n : nat) : Original_LF__DOT__Imp_LF_Imp_AExp_aevalR (Original_LF__DOT__Imp_LF_Imp_AExp_aexp.ANum n) n
  | E_APlus (e1 e2 : Original_LF__DOT__Imp_LF_Imp_AExp_aexp) (n1 n2 : nat) :
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR e1 n1 →
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR e2 n2 →
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR (Original_LF__DOT__Imp_LF_Imp_AExp_aexp.APlus e1 e2) (Nat_add n1 n2)
  | E_AMinus (e1 e2 : Original_LF__DOT__Imp_LF_Imp_AExp_aexp) (n1 n2 : nat) :
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR e1 n1 →
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR e2 n2 →
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR (Original_LF__DOT__Imp_LF_Imp_AExp_aexp.AMinus e1 e2) (Nat_sub n1 n2)
  | E_AMult (e1 e2 : Original_LF__DOT__Imp_LF_Imp_AExp_aexp) (n1 n2 : nat) :
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR e1 n1 →
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR e2 n2 →
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR (Original_LF__DOT__Imp_LF_Imp_AExp_aexp.AMult e1 e2) (Nat_mul n1 n2)

-- aevalR_first_try.aevalR - same structure
inductive Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_aevalR : Original_LF__DOT__Imp_LF_Imp_AExp_aexp → nat → Prop where
  | E_ANum (n : nat) : Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_aevalR (Original_LF__DOT__Imp_LF_Imp_AExp_aexp.ANum n) n
  | E_APlus (e1 e2 : Original_LF__DOT__Imp_LF_Imp_AExp_aexp) (n1 n2 : nat) :
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_aevalR e1 n1 →
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_aevalR e2 n2 →
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_aevalR (Original_LF__DOT__Imp_LF_Imp_AExp_aexp.APlus e1 e2) (Nat_add n1 n2)
  | E_AMinus (e1 e2 : Original_LF__DOT__Imp_LF_Imp_AExp_aexp) (n1 n2 : nat) :
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_aevalR e1 n1 →
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_aevalR e2 n2 →
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_aevalR (Original_LF__DOT__Imp_LF_Imp_AExp_aexp.AMinus e1 e2) (Nat_sub n1 n2)
  | E_AMult (e1 e2 : Original_LF__DOT__Imp_LF_Imp_AExp_aexp) (n1 n2 : nat) :
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_aevalR e1 n1 →
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_aevalR e2 n2 →
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_aevalR (Original_LF__DOT__Imp_LF_Imp_AExp_aexp.AMult e1 e2) (Nat_mul n1 n2)

-- aevalR_first_try.HypothesisNames.aevalR - same structure
inductive Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_HypothesisNames_aevalR : Original_LF__DOT__Imp_LF_Imp_AExp_aexp → nat → Prop where
  | E_ANum (n : nat) : Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_HypothesisNames_aevalR (Original_LF__DOT__Imp_LF_Imp_AExp_aexp.ANum n) n
  | E_APlus (e1 e2 : Original_LF__DOT__Imp_LF_Imp_AExp_aexp) (n1 n2 : nat) :
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_HypothesisNames_aevalR e1 n1 →
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_HypothesisNames_aevalR e2 n2 →
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_HypothesisNames_aevalR (Original_LF__DOT__Imp_LF_Imp_AExp_aexp.APlus e1 e2) (Nat_add n1 n2)
  | E_AMinus (e1 e2 : Original_LF__DOT__Imp_LF_Imp_AExp_aexp) (n1 n2 : nat) :
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_HypothesisNames_aevalR e1 n1 →
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_HypothesisNames_aevalR e2 n2 →
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_HypothesisNames_aevalR (Original_LF__DOT__Imp_LF_Imp_AExp_aexp.AMinus e1 e2) (Nat_sub n1 n2)
  | E_AMult (e1 e2 : Original_LF__DOT__Imp_LF_Imp_AExp_aexp) (n1 n2 : nat) :
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_HypothesisNames_aevalR e1 n1 →
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_HypothesisNames_aevalR e2 n2 →
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_HypothesisNames_aevalR (Original_LF__DOT__Imp_LF_Imp_AExp_aexp.AMult e1 e2) (Nat_mul n1 n2)

-- silly2 (admitted in Original.v)
axiom Original_LF__DOT__Imp_LF_Imp_AExp_silly2 : ∀ (ae : Original_LF__DOT__Imp_LF_Imp_AExp_aexp),
  Corelib_Init_Logic_eq (Original_LF__DOT__Imp_LF_Imp_AExp_aeval ae) (Original_LF__DOT__Imp_LF_Imp_AExp_aeval ae)

-- aevalR_iff_aeval (admitted in Original.v)
axiom Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__iff__aeval : ∀ (a : Original_LF__DOT__Imp_LF_Imp_AExp_aexp) (n : nat),
  iff (Original_LF__DOT__Imp_LF_Imp_AExp_aevalR a n) (Corelib_Init_Logic_eq (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a) n)

-- aevalR_iff_aeval' (admitted in Original.v)
axiom Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__iff__aeval' : ∀ (a : Original_LF__DOT__Imp_LF_Imp_AExp_aexp) (n : nat),
  iff (Original_LF__DOT__Imp_LF_Imp_AExp_aevalR a n) (Corelib_Init_Logic_eq (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a) n)

-- manual_grade_for_not_PNP_informal = None : option (nat * string)
def Original_LF__DOT__Logic_LF_Logic_manual__grade__for__not__PNP__informal :
    Original_LF__DOT__Poly_LF_Poly_option (Original_LF__DOT__Poly_LF_Poly_prod nat String_string) :=
  Original_LF__DOT__Poly_LF_Poly_option.None

-- relation from LF.Rel  
def Original_LF_Rel_relation (X : Type) := X → X → Prop

-- antisymmetric from LF.Rel
def Original_LF_Rel_antisymmetric {X : Type} (R : X → X → Prop) : Prop :=
  ∀ a b : X, R a b → R b a → Corelib_Init_Logic_eq a b



