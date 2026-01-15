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
-- Original.LF_DOT_AltAuto definitions  
-- ============================================================

-- nonzeros: filters out zeros from a list of nats
def Original_LF__DOT__AltAuto_LF_AltAuto_nonzeros : Original_LF__DOT__Poly_LF_Poly_list nat → Original_LF__DOT__Poly_LF_Poly_list nat
  | Original_LF__DOT__Poly_LF_Poly_list.nil => Original_LF__DOT__Poly_LF_Poly_list.nil
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t => 
    match h with
    | nat.O => Original_LF__DOT__AltAuto_LF_AltAuto_nonzeros t
    | nat.S _ => Original_LF__DOT__Poly_LF_Poly_list.cons h (Original_LF__DOT__AltAuto_LF_AltAuto_nonzeros t)

-- nonzeros_app is Admitted in Original.v, so we axiomatize it
axiom Original_LF__DOT__AltAuto_LF_AltAuto_nonzeros__app :
  ∀ (lst1 lst2 : Original_LF__DOT__Poly_LF_Poly_list nat),
    Corelib_Init_Logic_eq
      (Original_LF__DOT__AltAuto_LF_AltAuto_nonzeros (Original_LF__DOT__Poly_LF_Poly_app nat lst1 lst2))
      (Original_LF__DOT__Poly_LF_Poly_app nat (Original_LF__DOT__AltAuto_LF_AltAuto_nonzeros lst1) (Original_LF__DOT__AltAuto_LF_AltAuto_nonzeros lst2))

-- nor: neither P nor Q
def Original_LF__DOT__AltAuto_LF_AltAuto_nor (P Q : Prop) : Prop :=
  Logic_not P ∧ Logic_not Q

-- nor_not is Admitted in Original.v: forall P, nor P P <-> ~P
axiom Original_LF__DOT__AltAuto_LF_AltAuto_nor__not :
  ∀ (P : Prop), iff (Original_LF__DOT__AltAuto_LF_AltAuto_nor P P) (Logic_not P)

-- ============================================================
-- Original.LF_DOT_Basics extras (day, incr, etc.)
-- ============================================================

-- day type
inductive Original_LF__DOT__Basics_LF_Basics_day : Type where
  | monday : Original_LF__DOT__Basics_LF_Basics_day
  | tuesday : Original_LF__DOT__Basics_LF_Basics_day
  | wednesday : Original_LF__DOT__Basics_LF_Basics_day
  | thursday : Original_LF__DOT__Basics_LF_Basics_day
  | friday : Original_LF__DOT__Basics_LF_Basics_day
  | saturday : Original_LF__DOT__Basics_LF_Basics_day
  | sunday : Original_LF__DOT__Basics_LF_Basics_day

def Original_LF__DOT__Basics_LF_Basics_tuesday : Original_LF__DOT__Basics_LF_Basics_day := 
  Original_LF__DOT__Basics_LF_Basics_day.tuesday

def Original_LF__DOT__Basics_LF_Basics_saturday : Original_LF__DOT__Basics_LF_Basics_day := 
  Original_LF__DOT__Basics_LF_Basics_day.saturday

-- next_working_day
def Original_LF__DOT__Basics_LF_Basics_next__working__day (d : Original_LF__DOT__Basics_LF_Basics_day) : Original_LF__DOT__Basics_LF_Basics_day :=
  match d with
  | Original_LF__DOT__Basics_LF_Basics_day.monday => Original_LF__DOT__Basics_LF_Basics_day.tuesday
  | Original_LF__DOT__Basics_LF_Basics_day.tuesday => Original_LF__DOT__Basics_LF_Basics_day.wednesday
  | Original_LF__DOT__Basics_LF_Basics_day.wednesday => Original_LF__DOT__Basics_LF_Basics_day.thursday
  | Original_LF__DOT__Basics_LF_Basics_day.thursday => Original_LF__DOT__Basics_LF_Basics_day.friday
  | Original_LF__DOT__Basics_LF_Basics_day.friday => Original_LF__DOT__Basics_LF_Basics_day.monday
  | Original_LF__DOT__Basics_LF_Basics_day.saturday => Original_LF__DOT__Basics_LF_Basics_day.monday
  | Original_LF__DOT__Basics_LF_Basics_day.sunday => Original_LF__DOT__Basics_LF_Basics_day.monday

-- test_next_working_day is Admitted, so we axiomatize it
axiom Original_LF__DOT__Basics_LF_Basics_test__next__working__day :
  Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_next__working__day (Original_LF__DOT__Basics_LF_Basics_next__working__day Original_LF__DOT__Basics_LF_Basics_saturday)) Original_LF__DOT__Basics_LF_Basics_tuesday

-- bin type (binary numbers)
inductive Original_LF__DOT__Basics_LF_Basics_bin : Type where
  | Z : Original_LF__DOT__Basics_LF_Basics_bin
  | B0 : Original_LF__DOT__Basics_LF_Basics_bin → Original_LF__DOT__Basics_LF_Basics_bin
  | B1 : Original_LF__DOT__Basics_LF_Basics_bin → Original_LF__DOT__Basics_LF_Basics_bin

def Original_LF__DOT__Basics_LF_Basics_Z : Original_LF__DOT__Basics_LF_Basics_bin :=
  Original_LF__DOT__Basics_LF_Basics_bin.Z

def Original_LF__DOT__Basics_LF_Basics_B0 : Original_LF__DOT__Basics_LF_Basics_bin → Original_LF__DOT__Basics_LF_Basics_bin :=
  Original_LF__DOT__Basics_LF_Basics_bin.B0

def Original_LF__DOT__Basics_LF_Basics_B1 : Original_LF__DOT__Basics_LF_Basics_bin → Original_LF__DOT__Basics_LF_Basics_bin :=
  Original_LF__DOT__Basics_LF_Basics_bin.B1

-- incr: increment binary number
def Original_LF__DOT__Basics_LF_Basics_incr : Original_LF__DOT__Basics_LF_Basics_bin → Original_LF__DOT__Basics_LF_Basics_bin
  | Original_LF__DOT__Basics_LF_Basics_bin.Z => Original_LF__DOT__Basics_LF_Basics_bin.B1 Original_LF__DOT__Basics_LF_Basics_bin.Z
  | Original_LF__DOT__Basics_LF_Basics_bin.B0 b => Original_LF__DOT__Basics_LF_Basics_bin.B1 b
  | Original_LF__DOT__Basics_LF_Basics_bin.B1 b => Original_LF__DOT__Basics_LF_Basics_bin.B0 (Original_LF__DOT__Basics_LF_Basics_incr b)

-- test_bin_incr1 is Admitted, so we axiomatize it
axiom Original_LF__DOT__Basics_LF_Basics_test__bin__incr1 :
  Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_incr (Original_LF__DOT__Basics_LF_Basics_bin.B1 Original_LF__DOT__Basics_LF_Basics_bin.Z)) 
                        (Original_LF__DOT__Basics_LF_Basics_bin.B0 (Original_LF__DOT__Basics_LF_Basics_bin.B1 Original_LF__DOT__Basics_LF_Basics_bin.Z))

-- ============================================================
-- Original.LF_DOT_Lists.NatList definitions
-- ============================================================

-- natprod: pair of nats
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natprod : Type where
  | pair : nat → nat → Original_LF__DOT__Lists_LF_Lists_NatList_natprod

def Original_LF__DOT__Lists_LF_Lists_NatList_pair : nat → nat → Original_LF__DOT__Lists_LF_Lists_NatList_natprod :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natprod.pair

-- fst and snd
def Original_LF__DOT__Lists_LF_Lists_NatList_fst (p : Original_LF__DOT__Lists_LF_Lists_NatList_natprod) : nat :=
  match p with
  | Original_LF__DOT__Lists_LF_Lists_NatList_natprod.pair x _ => x

def Original_LF__DOT__Lists_LF_Lists_NatList_snd (p : Original_LF__DOT__Lists_LF_Lists_NatList_natprod) : nat :=
  match p with
  | Original_LF__DOT__Lists_LF_Lists_NatList_natprod.pair _ y => y

-- swap_pair
def Original_LF__DOT__Lists_LF_Lists_NatList_swap__pair (p : Original_LF__DOT__Lists_LF_Lists_NatList_natprod) : Original_LF__DOT__Lists_LF_Lists_NatList_natprod :=
  match p with
  | Original_LF__DOT__Lists_LF_Lists_NatList_natprod.pair x y => Original_LF__DOT__Lists_LF_Lists_NatList_natprod.pair y x

-- fst_swap_is_snd - can be computed
theorem Original_LF__DOT__Lists_LF_Lists_NatList_fst__swap__is__snd :
  ∀ (p : Original_LF__DOT__Lists_LF_Lists_NatList_natprod),
    Corelib_Init_Logic_eq (Original_LF__DOT__Lists_LF_Lists_NatList_fst (Original_LF__DOT__Lists_LF_Lists_NatList_swap__pair p))
                          (Original_LF__DOT__Lists_LF_Lists_NatList_snd p)
  | .pair _ _ => Corelib_Init_Logic_eq.refl _

-- natlist
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natlist : Type where
  | nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist

def Original_LF__DOT__Lists_LF_Lists_NatList_nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil

def Original_LF__DOT__Lists_LF_Lists_NatList_cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons

-- odd function (needed for oddmembers)
def Original_LF__DOT__Basics_LF_Basics_odd (n : nat) : Stdlib_bool :=
  match n with
  | nat.O => Stdlib_bool.false
  | nat.S nat.O => Stdlib_bool.true
  | nat.S (nat.S n') => Original_LF__DOT__Basics_LF_Basics_odd n'

-- oddmembers
def Original_LF__DOT__Lists_LF_Lists_NatList_oddmembers : Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil => Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h t =>
    match Original_LF__DOT__Basics_LF_Basics_odd h with
    | Stdlib_bool.true => Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h (Original_LF__DOT__Lists_LF_Lists_NatList_oddmembers t)
    | Stdlib_bool.false => Original_LF__DOT__Lists_LF_Lists_NatList_oddmembers t

-- ============================================================
-- Original.LF_DOT_Logic definitions
-- ============================================================

-- is_three
def Original_LF__DOT__Logic_LF_Logic_is__three (n : nat) : Prop :=
  Corelib_Init_Logic_eq n (nat.S (nat.S (nat.S nat.O)))

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

-- test_oddmembers - can be computed by native evaluation
theorem Original_LF__DOT__Lists_LF_Lists_NatList_test__oddmembers :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_oddmembers
      (Original_LF__DOT__Lists_LF_Lists_NatList_cons nat.O
        (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S nat.O)
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons nat.O
            (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S (nat.S nat.O))
              (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S (nat.S (nat.S nat.O)))
                (Original_LF__DOT__Lists_LF_Lists_NatList_cons nat.O
                  (Original_LF__DOT__Lists_LF_Lists_NatList_cons nat.O
                    Original_LF__DOT__Lists_LF_Lists_NatList_nil))))))))
    (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S nat.O)
      (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S (nat.S (nat.S nat.O)))
        Original_LF__DOT__Lists_LF_Lists_NatList_nil)) :=
  Corelib_Init_Logic_eq.refl _

-- ============================================================
-- Basics: plus, mult, factorial
-- ============================================================

def Original_LF__DOT__Basics_LF_Basics_plus : nat → nat → nat
  | nat.O, m => m
  | nat.S n', m => nat.S (Original_LF__DOT__Basics_LF_Basics_plus n' m)

def Original_LF__DOT__Basics_LF_Basics_mult : nat → nat → nat
  | nat.O, _ => nat.O
  | nat.S n', m => Original_LF__DOT__Basics_LF_Basics_plus m (Original_LF__DOT__Basics_LF_Basics_mult n' m)

def Original_LF__DOT__Basics_LF_Basics_factorial : nat → nat
  | nat.O => nat.S nat.O
  | nat.S n' => Original_LF__DOT__Basics_LF_Basics_mult (nat.S n') (Original_LF__DOT__Basics_LF_Basics_factorial n')

-- ============================================================
-- Poly: map, flat_map
-- ============================================================

def Original_LF__DOT__Poly_LF_Poly_map {X Y : Type} (f : X → Y) : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list Y
  | Original_LF__DOT__Poly_LF_Poly_list.nil => Original_LF__DOT__Poly_LF_Poly_list.nil
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t => Original_LF__DOT__Poly_LF_Poly_list.cons (f h) (Original_LF__DOT__Poly_LF_Poly_map f t)

def Original_LF__DOT__Poly_LF_Poly_flat__map {X Y : Type} (f : X → Original_LF__DOT__Poly_LF_Poly_list Y) : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list Y
  | Original_LF__DOT__Poly_LF_Poly_list.nil => Original_LF__DOT__Poly_LF_Poly_list.nil
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t => Original_LF__DOT__Poly_LF_Poly_app Y (f h) (Original_LF__DOT__Poly_LF_Poly_flat__map f t)

-- ============================================================
-- Tactics: foo
-- ============================================================

def five : nat := nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))

def Original_LF__DOT__Tactics_LF_Tactics_foo (_ : nat) : nat := five

-- silly_fact_1: forall m, foo m + 1 = foo (m + 1) + 1
-- This is Admitted in Original.v, so we use an axiom
axiom Original_LF__DOT__Tactics_LF_Tactics_silly__fact__1 :
  ∀ (m : nat), Corelib_Init_Logic_eq
    (Nat_add (Original_LF__DOT__Tactics_LF_Tactics_foo m) (nat.S nat.O))
    (Nat_add (Original_LF__DOT__Tactics_LF_Tactics_foo (Nat_add m (nat.S nat.O))) (nat.S nat.O))

-- ============================================================
-- ProofObjects: eq, eq_refl, eq_cons
-- ============================================================

inductive Original_LF__DOT__ProofObjects_LF_ProofObjects_eq {X : Type} (x : X) : X → Prop where
  | refl : Original_LF__DOT__ProofObjects_LF_ProofObjects_eq x x

def Original_LF__DOT__ProofObjects_LF_ProofObjects_eq__refl {X : Type} (x : X) : Original_LF__DOT__ProofObjects_LF_ProofObjects_eq x x :=
  Original_LF__DOT__ProofObjects_LF_ProofObjects_eq.refl

-- eq_cons: congruence lemma for cons
def Original_LF__DOT__ProofObjects_LF_ProofObjects_eq__cons {X : Type} (h1 h2 : X) (t1 t2 : Original_LF__DOT__Poly_LF_Poly_list X)
  (Hh : Original_LF__DOT__ProofObjects_LF_ProofObjects_eq h1 h2)
  (Ht : Original_LF__DOT__ProofObjects_LF_ProofObjects_eq t1 t2) :
  Original_LF__DOT__ProofObjects_LF_ProofObjects_eq 
    (Original_LF__DOT__Poly_LF_Poly_list.cons h1 t1)
    (Original_LF__DOT__Poly_LF_Poly_list.cons h2 t2) :=
  match Hh, Ht with
  | Original_LF__DOT__ProofObjects_LF_ProofObjects_eq.refl, Original_LF__DOT__ProofObjects_LF_ProofObjects_eq.refl => 
    Original_LF__DOT__ProofObjects_LF_ProofObjects_eq.refl

-- equality__leibniz_equality: Leibniz equality principle (admitted in Original.v)
axiom Original_LF__DOT__ProofObjects_LF_ProofObjects_equality____leibniz__equality :
  ∀ (X : Type) (x y : X),
    Original_LF__DOT__ProofObjects_LF_ProofObjects_eq x y → 
    ∀ (P : X → Prop), P x → P y

-- ============================================================
-- AltAuto: imp3
-- ============================================================

def Original_LF__DOT__AltAuto_LF_AltAuto_imp3 (P Q R : Prop) : (P → Q → R) → (Q → P → R) :=
  fun f q p => f p q

-- ============================================================
-- test_factorial2 (proof)
-- ============================================================

-- theorem test_factorial2 : factorial 5 = mult 10 12 is a simple equality check
-- In our nat representation, 5 = S(S(S(S(S(O))))), 10 = S^10(O), 12 = S^12(O)
-- factorial 5 = 120, mult 10 12 = 120
theorem Original_LF__DOT__Basics_LF_Basics_test__factorial2 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Basics_LF_Basics_factorial five)
    (Original_LF__DOT__Basics_LF_Basics_mult
      (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))))))))
      (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))))))))))) :=
  Corelib_Init_Logic_eq.refl _

-- ============================================================
-- test_flat_map1 (proof)
-- ============================================================

-- We need the original definition of flat_map being tested
-- test_flat_map1: flat_map (fun n => [n; n; n]) [1; 5; 4] = [1;1;1;5;5;5;4;4;4]
-- Using nat representation

def one : nat := nat.S nat.O
def four : nat := nat.S (nat.S (nat.S (nat.S nat.O)))

theorem Original_LF__DOT__Poly_LF_Poly_test__flat__map1 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Poly_LF_Poly_flat__map
      (fun n => Original_LF__DOT__Poly_LF_Poly_list.cons n
        (Original_LF__DOT__Poly_LF_Poly_list.cons n
          (Original_LF__DOT__Poly_LF_Poly_list.cons n Original_LF__DOT__Poly_LF_Poly_list.nil)))
      (Original_LF__DOT__Poly_LF_Poly_list.cons one
        (Original_LF__DOT__Poly_LF_Poly_list.cons five
          (Original_LF__DOT__Poly_LF_Poly_list.cons four Original_LF__DOT__Poly_LF_Poly_list.nil))))
    (Original_LF__DOT__Poly_LF_Poly_list.cons one
      (Original_LF__DOT__Poly_LF_Poly_list.cons one
        (Original_LF__DOT__Poly_LF_Poly_list.cons one
          (Original_LF__DOT__Poly_LF_Poly_list.cons five
            (Original_LF__DOT__Poly_LF_Poly_list.cons five
              (Original_LF__DOT__Poly_LF_Poly_list.cons five
                (Original_LF__DOT__Poly_LF_Poly_list.cons four
                  (Original_LF__DOT__Poly_LF_Poly_list.cons four
                    (Original_LF__DOT__Poly_LF_Poly_list.cons four Original_LF__DOT__Poly_LF_Poly_list.nil))))))))) :=
  Corelib_Init_Logic_eq.refl _

-- ============================================================
-- test_map1' (proof) - exercises
-- ============================================================

-- test_map1' : map (plus 3) [2;0;2] = [5;3;5]
def two : nat := nat.S (nat.S nat.O)
def three : nat := nat.S (nat.S (nat.S nat.O))

theorem Original_LF__DOT__Poly_LF_Poly_Exercises_test__map1' :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Poly_LF_Poly_map (Original_LF__DOT__Basics_LF_Basics_plus three)
      (Original_LF__DOT__Poly_LF_Poly_list.cons two
        (Original_LF__DOT__Poly_LF_Poly_list.cons nat.O
          (Original_LF__DOT__Poly_LF_Poly_list.cons two Original_LF__DOT__Poly_LF_Poly_list.nil))))
    (Original_LF__DOT__Poly_LF_Poly_list.cons five
      (Original_LF__DOT__Poly_LF_Poly_list.cons three
        (Original_LF__DOT__Poly_LF_Poly_list.cons five Original_LF__DOT__Poly_LF_Poly_list.nil))) :=
  Corelib_Init_Logic_eq.refl _

-- ============================================================
-- snd_fst_is_swap (proof)
-- ============================================================

theorem Original_LF__DOT__Lists_LF_Lists_NatList_snd__fst__is__swap :
  ∀ (p : Original_LF__DOT__Lists_LF_Lists_NatList_natprod),
    Corelib_Init_Logic_eq
      (Original_LF__DOT__Lists_LF_Lists_NatList_pair
        (Original_LF__DOT__Lists_LF_Lists_NatList_snd p)
        (Original_LF__DOT__Lists_LF_Lists_NatList_fst p))
      (Original_LF__DOT__Lists_LF_Lists_NatList_swap__pair p)
  | Original_LF__DOT__Lists_LF_Lists_NatList_natprod.pair n m => Corelib_Init_Logic_eq.refl _

-- ============================================================
-- mynil (monomorphic - list nat)
-- ============================================================

def Original_LF__DOT__Poly_LF_Poly_mynil : Original_LF__DOT__Poly_LF_Poly_list nat :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

