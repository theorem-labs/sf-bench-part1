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

-- Using change_names tool for bool/true/false mapping

-- Custom nat
inductive nat : Type where
  | O : nat
  | S : nat → nat

def zero_nat : nat := nat.O
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
-- Additional definitions for required isomorphisms
-- ============================================================

-- andb for Original.LF_DOT_Basics
def Original_LF__DOT__Basics_LF_Basics_andb (b1 b2 : Original_LF__DOT__Basics_LF_Basics_bool) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match b1 with
  | .true => b2
  | .false => .false

-- andb_commutative is Admitted
axiom Original_LF__DOT__AltAuto_LF_AltAuto_andb__commutative :
  ∀ b c : Original_LF__DOT__Basics_LF_Basics_bool,
    @Corelib_Init_Logic_eq Original_LF__DOT__Basics_LF_Basics_bool
      (Original_LF__DOT__Basics_LF_Basics_andb b c)
      (Original_LF__DOT__Basics_LF_Basics_andb c b)

-- le as a computational definition
def le (n m : nat) : Prop := 
  match n, m with
  | nat.O, _ => MyTrue
  | nat.S _, nat.O => MyFalse
  | nat.S n', nat.S m' => le n' m'

-- and in Prop
inductive and (A B : Prop) : Prop where
  | intro : A → B → and A B

-- auto_example_6' is Admitted
axiom Original_LF__DOT__Auto_LF_Auto_auto__example__6' :
  ∀ n m p : nat,
    (le n p → and (le n m) (le m n)) →
    le n p →
    @Corelib_Init_Logic_eq nat n m

-- cnat type (Church numerals)
def Original_LF__DOT__Poly_LF_Poly_Exercises_cnat : Type 1 := 
  (X : Type) → (X → X) → X → X

-- zero: cnat
def Original_LF__DOT__Poly_LF_Poly_Exercises_zero : Original_LF__DOT__Poly_LF_Poly_Exercises_cnat :=
  fun _ _ x => x

-- one: cnat
def Original_LF__DOT__Poly_LF_Poly_Exercises_one : Original_LF__DOT__Poly_LF_Poly_Exercises_cnat :=
  fun _ f x => f x

-- scc is Admitted
axiom Original_LF__DOT__Poly_LF_Poly_Exercises_scc :
  Original_LF__DOT__Poly_LF_Poly_Exercises_cnat →
  Original_LF__DOT__Poly_LF_Poly_Exercises_cnat

-- Equality for cnat
inductive Corelib_Init_Logic_eq_cnat : Original_LF__DOT__Poly_LF_Poly_Exercises_cnat → Original_LF__DOT__Poly_LF_Poly_Exercises_cnat → Prop where
  | refl (a : Original_LF__DOT__Poly_LF_Poly_Exercises_cnat) : Corelib_Init_Logic_eq_cnat a a

-- scc_1 is Admitted (scc zero = one)
axiom Original_LF__DOT__Poly_LF_Poly_Exercises_scc__1 :
  Corelib_Init_Logic_eq_cnat
    (Original_LF__DOT__Poly_LF_Poly_Exercises_scc Original_LF__DOT__Poly_LF_Poly_Exercises_zero)
    Original_LF__DOT__Poly_LF_Poly_Exercises_one

-- ev predicate
inductive Original_LF__DOT__ProofObjects_LF_ProofObjects_ev : nat → Prop where
  | ev_0 : Original_LF__DOT__ProofObjects_LF_ProofObjects_ev nat.O
  | ev_SS : ∀ n : nat, Original_LF__DOT__ProofObjects_LF_ProofObjects_ev n →
              Original_LF__DOT__ProofObjects_LF_ProofObjects_ev (nat.S (nat.S n))

-- ev_plus2'' type  
-- ev_plus2'' : forall n, ev n -> ev (n + 2)
-- The original definition proves this using ev_SS
-- We define it directly using ev_SS
def Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2'' :
  ∀ n : nat, Original_LF__DOT__ProofObjects_LF_ProofObjects_ev n →
    Original_LF__DOT__ProofObjects_LF_ProofObjects_ev (nat.S (nat.S n)) :=
  fun n evn => Original_LF__DOT__ProofObjects_LF_ProofObjects_ev.ev_SS n evn

-- natlist
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natlist : Type where
  | nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist

def Original_LF__DOT__Lists_LF_Lists_NatList_nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil

def Original_LF__DOT__Lists_LF_Lists_NatList_cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons

-- bag is alias for natlist
def Original_LF__DOT__Lists_LF_Lists_NatList_bag : Type := Original_LF__DOT__Lists_LF_Lists_NatList_natlist

-- count: counts occurrences of v in bag s
def Original_LF__DOT__Lists_LF_Lists_NatList_count (v : nat) (s : Original_LF__DOT__Lists_LF_Lists_NatList_bag) : nat :=
  match s with
  | .nil => nat.O
  | .cons h t => 
    match Nat_eqb v h with
    | Stdlib_bool.true => nat.S (Original_LF__DOT__Lists_LF_Lists_NatList_count v t)
    | Stdlib_bool.false => Original_LF__DOT__Lists_LF_Lists_NatList_count v t

-- remove_all is Admitted
axiom Original_LF__DOT__Lists_LF_Lists_NatList_remove__all : nat → Original_LF__DOT__Lists_LF_Lists_NatList_bag → Original_LF__DOT__Lists_LF_Lists_NatList_bag

-- test_remove_all4 is Admitted
axiom Original_LF__DOT__Lists_LF_Lists_NatList_test__remove__all4 :
  @Corelib_Init_Logic_eq nat
    (Original_LF__DOT__Lists_LF_Lists_NatList_count 
       (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))  -- 5
       (Original_LF__DOT__Lists_LF_Lists_NatList_remove__all 
          (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))  -- 5
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S (nat.S nat.O))  -- 2
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S nat.O)  -- 1
                (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))  -- 5
                   (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S (nat.S (nat.S (nat.S nat.O))))  -- 4
                      (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))  -- 5
                         (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S nat.O)  -- 1
                            (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S (nat.S (nat.S (nat.S nat.O))))  -- 4
                               (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))  -- 5
                                  (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S nat.O)  -- 1
                                     (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S (nat.S (nat.S (nat.S nat.O))))  -- 4
                                        Original_LF__DOT__Lists_LF_Lists_NatList_nil))))))))))))
    nat.O  -- 0

-- In predicate for Logic
def Original_LF__DOT__Logic_LF_Logic_In {A : Type} (x : A) (l : Original_LF__DOT__Poly_LF_Poly_list A) : Prop :=
  match l with
  | .nil => Original_False
  | .cons h t => h = x ∨ Original_LF__DOT__Logic_LF_Logic_In x t

-- map function
def Original_LF__DOT__Poly_LF_Poly_map {X Y : Type} (f : X → Y) : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list Y
  | .nil => .nil
  | .cons h t => .cons (f h) (Original_LF__DOT__Poly_LF_Poly_map f t)

-- In_map is Admitted
axiom Original_LF__DOT__Logic_LF_Logic_In__map :
  ∀ (A B : Type) (f : A → B) (l : Original_LF__DOT__Poly_LF_Poly_list A) (x : A),
    Original_LF__DOT__Logic_LF_Logic_In x l →
    Original_LF__DOT__Logic_LF_Logic_In (f x) (Original_LF__DOT__Poly_LF_Poly_map f l)

-- In10 axiom for Imp.AExp
def List_In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | list.nil => _root_.False
  | list.cons h t => h = x ∨ List_In x t

-- In10 is Admitted  
axiom Original_LF__DOT__Imp_LF_Imp_AExp_In10 :
  List_In
    (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))))))))  -- 10
    (list.cons (nat.S nat.O)  -- 1
      (list.cons (nat.S (nat.S nat.O))  -- 2
        (list.cons (nat.S (nat.S (nat.S nat.O)))  -- 3
          (list.cons (nat.S (nat.S (nat.S (nat.S nat.O))))  -- 4
            (list.cons (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))  -- 5
              (list.cons (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))))  -- 6
                (list.cons (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))))  -- 7
                  (list.cons (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))))))  -- 8
                    (list.cons (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))))))  -- 9
                      (list.cons (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))))))))  -- 10
                        list.nil))))))))))

-- option type
inductive option (A : Type) : Type where
  | none : option A
  | some : A → option A

def None {A : Type} : option A := option.none
def Some {A : Type} (a : A) : option A := option.some a

-- manual_grade_for_eqb_refl_informal 
def Original_LF__DOT__Induction_LF_Induction_manual__grade__for__eqb__refl__informal : 
  option (prod nat String_string) := option.none

-- ============================================================
-- Lists NatList definitions
-- ============================================================

-- add: adds an element to a bag (cons)
def Original_LF__DOT__Lists_LF_Lists_NatList_add (v : nat) (s : Original_LF__DOT__Lists_LF_Lists_NatList_natlist) : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons v s

-- Helper to compute length of natlist as Nat
def natlist_length : Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Nat
  | .nil => 0
  | .cons _ t => 1 + natlist_length t

-- alternate with fuel
def alternate_aux : Nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | 0, _, l2 => l2  -- should not happen with enough fuel
  | _, .nil, l2 => l2
  | n+1, .cons h1 t1, l2 => .cons h1 (alternate_aux n l2 t1)

-- alternate: alternates elements from two lists  
def Original_LF__DOT__Lists_LF_Lists_NatList_alternate (l1 l2 : Original_LF__DOT__Lists_LF_Lists_NatList_natlist) : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  alternate_aux (natlist_length l1 + natlist_length l2 + 1) l1 l2

-- remove_one: removes one occurrence of v from bag s
def Original_LF__DOT__Lists_LF_Lists_NatList_remove__one (v : nat) (s : Original_LF__DOT__Lists_LF_Lists_NatList_natlist) : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  match s with
  | .nil => .nil
  | .cons h t =>
    match Nat_eqb v h with
    | Stdlib_bool.true => t
    | Stdlib_bool.false => .cons h (Original_LF__DOT__Lists_LF_Lists_NatList_remove__one v t)

-- included: checks if bag s1 is included in bag s2
def Original_LF__DOT__Lists_LF_Lists_NatList_included : Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Basics_LF_Basics_bool
  | .nil, _ => .true
  | .cons h t, s2 =>
    match Nat_leb (nat.S nat.O) (Original_LF__DOT__Lists_LF_Lists_NatList_count h s2) with
    | Stdlib_bool.true => Original_LF__DOT__Lists_LF_Lists_NatList_included t (Original_LF__DOT__Lists_LF_Lists_NatList_remove__one h s2)
    | Stdlib_bool.false => .false

-- andb_commutative': proof that andb is commutative
theorem Original_LF__DOT__AltAuto_LF_AltAuto_andb__commutative' : ∀ b c : Original_LF__DOT__Basics_LF_Basics_bool, 
  @Corelib_Init_Logic_eq Original_LF__DOT__Basics_LF_Basics_bool 
    (Original_LF__DOT__Basics_LF_Basics_andb b c) (Original_LF__DOT__Basics_LF_Basics_andb c b) := 
  fun b c => match b, c with
  | .true, .true => Corelib_Init_Logic_eq.refl _
  | .true, .false => Corelib_Init_Logic_eq.refl _
  | .false, .true => Corelib_Init_Logic_eq.refl _
  | .false, .false => Corelib_Init_Logic_eq.refl _

-- ev_8': proof that 8 is even
def Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__8' : Original_LF__DOT__ProofObjects_LF_ProofObjects_ev (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))))) :=
  .ev_SS _ (.ev_SS _ (.ev_SS _ (.ev_SS _ .ev_0)))

-- Test definitions (these are the actual theorems we need to prove)
theorem Original_LF__DOT__Lists_LF_Lists_NatList_test__add1 : 
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__Lists_LF_Lists_NatList_count (nat.S nat.O) 
      (Original_LF__DOT__Lists_LF_Lists_NatList_add (nat.S nat.O) 
        (.cons (nat.S nat.O) (.cons (nat.S (nat.S (nat.S (nat.S nat.O)))) (.cons (nat.S nat.O) .nil)))))
    (nat.S (nat.S (nat.S nat.O))) := Corelib_Init_Logic_eq.refl _

theorem Original_LF__DOT__Lists_LF_Lists_NatList_test__alternate1 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_alternate 
      (.cons (nat.S nat.O) (.cons (nat.S (nat.S nat.O)) (.cons (nat.S (nat.S (nat.S nat.O))) .nil)))
      (.cons (nat.S (nat.S (nat.S (nat.S nat.O)))) (.cons (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))) (.cons (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))) .nil))))
    (.cons (nat.S nat.O) (.cons (nat.S (nat.S (nat.S (nat.S nat.O)))) (.cons (nat.S (nat.S nat.O)) (.cons (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))) (.cons (nat.S (nat.S (nat.S nat.O))) (.cons (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))) .nil)))))) := Corelib_Init_Logic_eq.refl _

theorem Original_LF__DOT__Lists_LF_Lists_NatList_test__alternate3 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_alternate 
      (.cons (nat.S nat.O) (.cons (nat.S (nat.S nat.O)) (.cons (nat.S (nat.S (nat.S nat.O))) .nil)))
      (.cons (nat.S (nat.S (nat.S (nat.S nat.O)))) .nil))
    (.cons (nat.S nat.O) (.cons (nat.S (nat.S (nat.S (nat.S nat.O)))) (.cons (nat.S (nat.S nat.O)) (.cons (nat.S (nat.S (nat.S nat.O))) .nil)))) := Corelib_Init_Logic_eq.refl _

theorem Original_LF__DOT__Lists_LF_Lists_NatList_test__count1 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_count (nat.S nat.O)
      (.cons (nat.S nat.O) (.cons (nat.S (nat.S nat.O)) (.cons (nat.S (nat.S (nat.S nat.O))) (.cons (nat.S nat.O) (.cons (nat.S (nat.S (nat.S (nat.S nat.O)))) (.cons (nat.S nat.O) .nil)))))))
    (nat.S (nat.S (nat.S nat.O))) := Corelib_Init_Logic_eq.refl _

theorem Original_LF__DOT__Lists_LF_Lists_NatList_test__included2 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_included
      (.cons (nat.S nat.O) (.cons (nat.S (nat.S nat.O)) (.cons (nat.S (nat.S nat.O)) .nil)))
      (.cons (nat.S (nat.S nat.O)) (.cons (nat.S nat.O) (.cons (nat.S (nat.S (nat.S (nat.S nat.O)))) (.cons (nat.S nat.O) .nil)))))
    Original_LF__DOT__Basics_LF_Basics_bool.false := Corelib_Init_Logic_eq.refl _

theorem Original_LF__DOT__Lists_LF_Lists_NatList_test__remove__one1 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_count (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))
      (Original_LF__DOT__Lists_LF_Lists_NatList_remove__one (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))
        (.cons (nat.S (nat.S nat.O)) (.cons (nat.S nat.O) (.cons (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))) (.cons (nat.S (nat.S (nat.S (nat.S nat.O)))) (.cons (nat.S nat.O) .nil)))))))
    nat.O := Corelib_Init_Logic_eq.refl _

theorem Original_LF__DOT__Lists_LF_Lists_NatList_test__remove__one4 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_count (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))
      (Original_LF__DOT__Lists_LF_Lists_NatList_remove__one (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))
        (.cons (nat.S (nat.S nat.O)) (.cons (nat.S nat.O) (.cons (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))) (.cons (nat.S (nat.S (nat.S (nat.S nat.O)))) (.cons (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))) (.cons (nat.S nat.O) (.cons (nat.S (nat.S (nat.S (nat.S nat.O)))) .nil)))))))))
    (nat.S nat.O) := Corelib_Init_Logic_eq.refl _

