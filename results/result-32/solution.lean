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
-- Original.LF.Rel definitions (Relations)
-- ============================================================

-- relation type
def Original_LF_Rel_relation (X : Type) : Type := X → X → Prop

-- next_nat relation
inductive Original_LF_Rel_next__nat : nat → nat → Prop where
  | nn (n : nat) : Original_LF_Rel_next__nat n (nat.S n)

-- partial_function predicate
def Original_LF_Rel_partial__function {X : Type} (R : X → X → Prop) : Prop :=
  ∀ (x y1 y2 : X), R x y1 → R x y2 → @Corelib_Init_Logic_eq X y1 y2

-- next_nat_partial_function theorem (axiom in Original)
axiom Original_LF_Rel_next__nat__partial__function :
  Original_LF_Rel_partial__function Original_LF_Rel_next__nat

-- ============================================================
-- Original.LF_DOT_Lists.LF.Lists.NatList definitions
-- ============================================================

-- natprod type
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natprod : Type where
  | pair : nat → nat → Original_LF__DOT__Lists_LF_Lists_NatList_natprod

def Original_LF__DOT__Lists_LF_Lists_NatList_pair : nat → nat → Original_LF__DOT__Lists_LF_Lists_NatList_natprod :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natprod.pair

def Original_LF__DOT__Lists_LF_Lists_NatList_fst (p : Original_LF__DOT__Lists_LF_Lists_NatList_natprod) : nat :=
  match p with
  | Original_LF__DOT__Lists_LF_Lists_NatList_natprod.pair n _ => n

def Original_LF__DOT__Lists_LF_Lists_NatList_snd (p : Original_LF__DOT__Lists_LF_Lists_NatList_natprod) : nat :=
  match p with
  | Original_LF__DOT__Lists_LF_Lists_NatList_natprod.pair _ m => m

-- surjective_pairing' theorem: for x x0 : nat, pair x x0 = pair (fst (pair x x0)) (snd (pair x x0))
-- This simplifies to pair x x0 = pair x x0, which is refl
theorem Original_LF__DOT__Lists_LF_Lists_NatList_surjective__pairingSQUOTE (x x0 : nat) :
  @Corelib_Init_Logic_eq Original_LF__DOT__Lists_LF_Lists_NatList_natprod
    (Original_LF__DOT__Lists_LF_Lists_NatList_pair x x0)
    (Original_LF__DOT__Lists_LF_Lists_NatList_pair
      (Original_LF__DOT__Lists_LF_Lists_NatList_fst (Original_LF__DOT__Lists_LF_Lists_NatList_pair x x0))
      (Original_LF__DOT__Lists_LF_Lists_NatList_snd (Original_LF__DOT__Lists_LF_Lists_NatList_pair x x0))) :=
  Corelib_Init_Logic_eq.refl _

-- ============================================================
-- Original.LF_DOT_Basics negb
-- ============================================================

def Original_LF__DOT__Basics_LF_Basics_negb (b : Original_LF__DOT__Basics_LF_Basics_bool) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match b with
  | Original_LF__DOT__Basics_LF_Basics_bool.true => Original_LF__DOT__Basics_LF_Basics_bool.false
  | Original_LF__DOT__Basics_LF_Basics_bool.false => Original_LF__DOT__Basics_LF_Basics_bool.true

-- ============================================================
-- no_whiles and no_whilesR for Imp
-- ============================================================

-- no_whiles function
def Original_LF__DOT__Imp_LF_Imp_no__whiles : Original_LF__DOT__Imp_LF_Imp_com → Stdlib_bool
  | Original_LF__DOT__Imp_LF_Imp_com.CSkip => Stdlib_bool.true
  | Original_LF__DOT__Imp_LF_Imp_com.CAsgn _ _ => Stdlib_bool.true
  | Original_LF__DOT__Imp_LF_Imp_com.CSeq c1 c2 => andb (Original_LF__DOT__Imp_LF_Imp_no__whiles c1) (Original_LF__DOT__Imp_LF_Imp_no__whiles c2)
  | Original_LF__DOT__Imp_LF_Imp_com.CIf _ c1 c2 => andb (Original_LF__DOT__Imp_LF_Imp_no__whiles c1) (Original_LF__DOT__Imp_LF_Imp_no__whiles c2)
  | Original_LF__DOT__Imp_LF_Imp_com.CWhile _ _ => Stdlib_bool.false

-- no_whilesR inductive predicate (empty - no constructors, while always fails)
inductive Original_LF__DOT__Imp_LF_Imp_no__whilesR : Original_LF__DOT__Imp_LF_Imp_com → Prop where
  -- no constructors - similar to False

-- no_whiles_eqv axiom
axiom Original_LF__DOT__Imp_LF_Imp_no__whiles__eqv (c : Original_LF__DOT__Imp_LF_Imp_com) :
  iff (@Corelib_Init_Logic_eq Stdlib_bool (Original_LF__DOT__Imp_LF_Imp_no__whiles c) Stdlib_bool.true)
      (Original_LF__DOT__Imp_LF_Imp_no__whilesR c)

-- ============================================================
-- Aliases for bool true/false
-- ============================================================

def mybool_true : Stdlib_bool := Stdlib_bool.true
def mybool_false : Stdlib_bool := Stdlib_bool.false
def mybool_andb : Stdlib_bool → Stdlib_bool → Stdlib_bool := andb

-- ============================================================
-- AltAuto theorems
-- ============================================================

-- negb_involutive theorem
theorem Original_LF__DOT__AltAuto_LF_AltAuto_negb__involutive (b : Original_LF__DOT__Basics_LF_Basics_bool) :
  @Corelib_Init_Logic_eq Original_LF__DOT__Basics_LF_Basics_bool
    (Original_LF__DOT__Basics_LF_Basics_negb (Original_LF__DOT__Basics_LF_Basics_negb b))
    b :=
  match b with
  | Original_LF__DOT__Basics_LF_Basics_bool.true => Corelib_Init_Logic_eq.refl _
  | Original_LF__DOT__Basics_LF_Basics_bool.false => Corelib_Init_Logic_eq.refl _

-- auto_example_1 theorem
theorem Original_LF__DOT__AltAuto_LF_AltAuto_auto__example__1 :
  ∀ (P Q R : Prop), (P → Q) → (Q → R) → P → R :=
  fun _ _ _ hpq hqr hp => hqr (hpq hp)

-- ============================================================
-- Induction theorem
-- ============================================================

-- Helper: congruence for S
def Corelib_Init_Logic_eq_S_cong {n m : nat} (h : @Corelib_Init_Logic_eq nat n m) :
  @Corelib_Init_Logic_eq nat (nat.S n) (nat.S m) :=
  match h with
  | Corelib_Init_Logic_eq.refl _ => Corelib_Init_Logic_eq.refl _

-- Helper: n + 0 = n
def Nat_add_zero_r : (n : nat) → @Corelib_Init_Logic_eq nat (Nat_add n nat.O) n
  | nat.O => Corelib_Init_Logic_eq.refl nat.O
  | nat.S n' => Corelib_Init_Logic_eq_S_cong (Nat_add_zero_r n')

-- mult_1_l theorem: 1 * n = n
-- Note: Nat_mul (S O) n = Nat_add n (Nat_mul O n) = Nat_add n O
theorem Original_LF__DOT__Induction_LF_Induction_mult__1__l (n : nat) :
  @Corelib_Init_Logic_eq nat (Nat_mul (nat.S nat.O) n) n :=
  Nat_add_zero_r n

-- ============================================================
-- Logic theorem
-- ============================================================

-- disc_example theorem
-- disc_example: forall n, 0 = S n -> False
theorem Original_LF__DOT__Logic_LF_Logic_disc__example :
  ∀ (n : nat), @Corelib_Init_Logic_eq nat nat.O (nat.S n) → MyFalse :=
  fun _ h => nomatch h

-- ============================================================
-- Poly definitions
-- ============================================================

-- option type
inductive Original_LF__DOT__Poly_LF_Poly_option (X : Type) : Type where
  | None : Original_LF__DOT__Poly_LF_Poly_option X
  | Some : X → Original_LF__DOT__Poly_LF_Poly_option X

def Original_LF__DOT__Poly_LF_Poly_None (X : Type) : Original_LF__DOT__Poly_LF_Poly_option X :=
  Original_LF__DOT__Poly_LF_Poly_option.None

-- prod type
inductive Original_LF__DOT__Poly_LF_Poly_prod (X Y : Type) : Type where
  | pair : X → Y → Original_LF__DOT__Poly_LF_Poly_prod X Y

-- ============================================================
-- Tactics theorem
-- ============================================================

-- manual_grade_for_split_combine is just None
def Original_LF__DOT__Tactics_LF_Tactics_manual__grade__for__split__combine : Original_LF__DOT__Poly_LF_Poly_option (Original_LF__DOT__Poly_LF_Poly_prod nat String_string) := Original_LF__DOT__Poly_LF_Poly_option.None

-- ============================================================
-- Relation definitions (for Rel module)
-- ============================================================

-- Reflexive property
def Original_LF_Rel_reflexive {X : Type} (R : X → X → Prop) : Prop :=
  ∀ a : X, R a a

-- Transitive property
def Original_LF_Rel_transitive {X : Type} (R : X → X → Prop) : Prop :=
  ∀ a b c : X, R a b → R b c → R a c

-- Antisymmetric property
def Original_LF_Rel_antisymmetric {X : Type} (R : X → X → Prop) : Prop :=
  ∀ a b : X, R a b → R b a → @Corelib_Init_Logic_eq X a b

-- Order property (reflexive + antisymmetric + transitive)
def Original_LF_Rel_order {X : Type} (R : X → X → Prop) : Prop :=
  Original_LF_Rel_reflexive R ∧ Original_LF_Rel_antisymmetric R ∧ Original_LF_Rel_transitive R

-- ============================================================
-- IndProp definitions (le, lt, R, fR)
-- ============================================================

-- le: less-than-or-equal relation on nat
inductive Original_LF__DOT__IndProp_LF_IndProp_le : nat → nat → Prop where
  | le_n : ∀ n, Original_LF__DOT__IndProp_LF_IndProp_le n n
  | le_S : ∀ n m, Original_LF__DOT__IndProp_LF_IndProp_le n m → Original_LF__DOT__IndProp_LF_IndProp_le n (nat.S m)

-- lt: strictly less-than relation on nat (n < m := S n <= m)
def Original_LF__DOT__IndProp_LF_IndProp_lt (n m : nat) : Prop :=
  Original_LF__DOT__IndProp_LF_IndProp_le (nat.S n) m

-- R relation (for R_equiv_fR theorem)
inductive Original_LF__DOT__IndProp_LF_IndProp_R : nat → nat → nat → Prop where
  | c1 : Original_LF__DOT__IndProp_LF_IndProp_R nat.O nat.O nat.O
  | c2 : ∀ m n o, Original_LF__DOT__IndProp_LF_IndProp_R m n o →
                   Original_LF__DOT__IndProp_LF_IndProp_R (nat.S m) n (nat.S o)
  | c3 : ∀ m n o, Original_LF__DOT__IndProp_LF_IndProp_R m n o →
                   Original_LF__DOT__IndProp_LF_IndProp_R m (nat.S n) (nat.S o)
  | c4 : ∀ m n o, Original_LF__DOT__IndProp_LF_IndProp_R (nat.S m) (nat.S n) (nat.S (nat.S o)) →
                   Original_LF__DOT__IndProp_LF_IndProp_R m n o
  | c5 : ∀ m n o, Original_LF__DOT__IndProp_LF_IndProp_R m n o →
                   Original_LF__DOT__IndProp_LF_IndProp_R n m o

-- fR function (the functional version of R)
def Original_LF__DOT__IndProp_LF_IndProp_fR : nat → nat → nat := Nat_add

-- ============================================================
-- ProofObjects definitions
-- ============================================================

-- or in ProofObjects.Props
inductive Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or (P Q : Prop) : Prop where
  | or_introl : P → Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or P Q
  | or_intror : Q → Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or P Q

-- ============================================================
-- Admitted Theorems (from Original.v)
-- ============================================================

-- le_reflexive: reflexive le (Admitted in Original.v)
axiom Original_LF_Rel_le__reflexive : Original_LF_Rel_reflexive Original_LF__DOT__IndProp_LF_IndProp_le

-- le_trans: transitive le (Admitted in Original.v)
axiom Original_LF_Rel_le__trans : Original_LF_Rel_transitive Original_LF__DOT__IndProp_LF_IndProp_le

-- lt_trans: transitive lt (Admitted in Original.v)
axiom Original_LF_Rel_lt__trans : Original_LF_Rel_transitive Original_LF__DOT__IndProp_LF_IndProp_lt

-- lt_trans'': transitive lt (Admitted in Original.v)
-- NOTE: After export, manually edit Imported.out to rename:
-- Original_LF_Rel_lt__transSQUOTESQUOTE -> Original_LF_Rel_lt__trans''
-- using: sed -i "s/Original_LF_Rel_lt__transSQUOTESQUOTE/Original_LF_Rel_lt__trans''/g" /workdir/Imported.out
axiom Original_LF_Rel_lt__transSQUOTESQUOTE : Original_LF_Rel_transitive Original_LF__DOT__IndProp_LF_IndProp_lt

-- le_antisymmetric: antisymmetric le (Admitted in Original.v)
axiom Original_LF_Rel_le__antisymmetric : Original_LF_Rel_antisymmetric Original_LF__DOT__IndProp_LF_IndProp_le

-- le_order: order le (Admitted in Original.v)
axiom Original_LF_Rel_le__order : Original_LF_Rel_order Original_LF__DOT__IndProp_LF_IndProp_le

-- R_equiv_fR: forall m n o, R m n o <-> fR m n = o (Admitted in Original.v)
axiom Original_LF__DOT__IndProp_LF_IndProp_R__equiv__fR :
  ∀ (m n o : nat), iff (Original_LF__DOT__IndProp_LF_IndProp_R m n o) 
                        (@Corelib_Init_Logic_eq nat (Original_LF__DOT__IndProp_LF_IndProp_fR m n) o)

-- surjective_pairing: forall (p : natprod), p = (fst p, snd p) (Admitted in Original.v)
axiom Original_LF__DOT__Lists_LF_Lists_NatList_surjective__pairing :
  ∀ (p : Original_LF__DOT__Lists_LF_Lists_NatList_natprod),
    @Corelib_Init_Logic_eq Original_LF__DOT__Lists_LF_Lists_NatList_natprod 
      p 
      (Original_LF__DOT__Lists_LF_Lists_NatList_pair 
        (Original_LF__DOT__Lists_LF_Lists_NatList_fst p) 
        (Original_LF__DOT__Lists_LF_Lists_NatList_snd p))

-- iff_trans: forall P Q R, (P <-> Q) -> (Q <-> R) -> (P <-> R) (Admitted in Original.v)
axiom Original_LF__DOT__Logic_LF_Logic_iff__trans :
  ∀ (P Q R : Prop), iff P Q → iff Q R → iff P R

-- or_elim (Definition in Original.v, not Admitted)
def Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or__elim 
    (P Q R : Prop) 
    (HPQ : Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or P Q) 
    (HPR : P → R) 
    (HQR : Q → R) : R :=
  match HPQ with
  | .or_introl HP => HPR HP
  | .or_intror HQ => HQR HQ

