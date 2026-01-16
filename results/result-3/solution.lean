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
structure Ascii_ascii : Type where
  b0 : Stdlib_bool
  b1 : Stdlib_bool
  b2 : Stdlib_bool
  b3 : Stdlib_bool
  b4 : Stdlib_bool
  b5 : Stdlib_bool
  b6 : Stdlib_bool
  b7 : Stdlib_bool

def Ascii_Ascii := Ascii_ascii.mk

-- Ascii equality
def Ascii_eqb (a1 a2 : Ascii_ascii) : Stdlib_bool :=
    andb (Bool_eqb a1.b0 a2.b0)
      (andb (Bool_eqb a1.b1 a2.b1)
        (andb (Bool_eqb a1.b2 a2.b2)
          (andb (Bool_eqb a1.b3 a2.b3)
            (andb (Bool_eqb a1.b4 a2.b4)
              (andb (Bool_eqb a1.b5 a2.b5)
                (andb (Bool_eqb a1.b6 a2.b6)
                  (Bool_eqb a1.b7 a2.b7)))))))

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
  intro ::
  mp : A → B
  mpr : B → A

def iff_intro := @iff.intro

-- and (logical conjunction)
inductive and (A B : Prop) : Prop where
  | intro : A → B → and A B

def and_intro := @and.intro

-- or (logical disjunction) - Church-encoded to work with SProp elimination
structure or (A B : Prop) : Prop where
  intro ::
  elim : ∀ C : Prop, (A → C) → (B → C) → C

-- Smart constructors for or
def or_inl {A B : Prop} (a : A) : or A B := ⟨fun _ f _ => f a⟩
def or_inr {A B : Prop} (b : B) : or A B := ⟨fun _ _ g => g b⟩

-- Keep the names that the export expects
def or_intro := @or.intro
def or_intror := @or_inr

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

-- List_In (membership in list)
def List_In {A : Type} (a : A) : list A → Prop
  | list.nil => MyFalse
  | list.cons h t => or (Corelib_Init_Logic_eq a h) (List_In a t)

-- option (stdlib version)
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
def charX : Ascii_ascii := ⟨Stdlib_bool.false, Stdlib_bool.false, Stdlib_bool.false, Stdlib_bool.true, Stdlib_bool.true, Stdlib_bool.false, Stdlib_bool.true, Stdlib_bool.false⟩
-- 'Y' = 89 = 0b01011001, LSB first: 1,0,0,1,1,0,1,0
def charY : Ascii_ascii := ⟨Stdlib_bool.true, Stdlib_bool.false, Stdlib_bool.false, Stdlib_bool.true, Stdlib_bool.true, Stdlib_bool.false, Stdlib_bool.true, Stdlib_bool.false⟩
-- 'Z' = 90 = 0b01011010, LSB first: 0,1,0,1,1,0,1,0
def charZ : Ascii_ascii := ⟨Stdlib_bool.false, Stdlib_bool.true, Stdlib_bool.false, Stdlib_bool.true, Stdlib_bool.true, Stdlib_bool.false, Stdlib_bool.true, Stdlib_bool.false⟩

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
-- Original.LF_DOT_Lists.LF.Lists.NatList definitions
-- ============================================================

-- natlist (list of nats)
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natlist : Type where
  | nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist

def Original_LF__DOT__Lists_LF_Lists_NatList_nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil

def Original_LF__DOT__Lists_LF_Lists_NatList_cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons

def Original_LF__DOT__Lists_LF_Lists_NatList_app : Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil, l2 => l2
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h t, l2 => 
      Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h (Original_LF__DOT__Lists_LF_Lists_NatList_app t l2)

def Original_LF__DOT__Lists_LF_Lists_NatList_rev : Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil => Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h t => 
      Original_LF__DOT__Lists_LF_Lists_NatList_app 
        (Original_LF__DOT__Lists_LF_Lists_NatList_rev t) 
        (Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil)

-- test_rev2 : rev [1;2;3] = [3;2;1] (Admitted)
axiom Original_LF__DOT__Lists_LF_Lists_NatList_test__rev2 : 
  @Corelib_Init_Logic_eq Original_LF__DOT__Lists_LF_Lists_NatList_natlist
    (Original_LF__DOT__Lists_LF_Lists_NatList_rev 
      (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S nat.O)
        (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S (nat.S nat.O))
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S (nat.S (nat.S nat.O)))
            Original_LF__DOT__Lists_LF_Lists_NatList_nil))))
    (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S (nat.S (nat.S nat.O)))
      (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S (nat.S nat.O))
        (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S nat.O)
          Original_LF__DOT__Lists_LF_Lists_NatList_nil)))

-- ============================================================
-- Original.LF_DOT_Induction definitions
-- ============================================================

def Original_LF__DOT__Induction_LF_Induction_double : nat → nat
  | nat.O => nat.O
  | nat.S n' => nat.S (nat.S (Original_LF__DOT__Induction_LF_Induction_double n'))

-- double_incr : forall n, double (S n) = S (S (double n)) (Admitted)
axiom Original_LF__DOT__Induction_LF_Induction_double__incr :
  ∀ (n : nat),
    @Corelib_Init_Logic_eq nat
      (Original_LF__DOT__Induction_LF_Induction_double (nat.S n))
      (nat.S (nat.S (Original_LF__DOT__Induction_LF_Induction_double n)))

-- ============================================================
-- Original.LF_DOT_Poly.Exercises (Church numerals)
-- ============================================================

def Original_LF__DOT__Poly_LF_Poly_Exercises_cnat : Type 1 := 
  (X : Type) → (X → X) → X → X

def Original_LF__DOT__Poly_LF_Poly_Exercises_zero : 
  (X : Type) → (X → X) → X → X :=
  fun (X : Type) (_ : X → X) (x : X) => x

-- zero_church_peano : zero nat S O = 0 (Admitted)
axiom Original_LF__DOT__Poly_LF_Poly_Exercises_zero__church__peano : 
  @Corelib_Init_Logic_eq nat
    (Original_LF__DOT__Poly_LF_Poly_Exercises_zero nat nat.S nat.O)
    nat.O

-- ============================================================
-- Original.LF_DOT_ProofObjects definitions
-- ============================================================

-- ProofObjects.eq (different from Corelib eq)
inductive Original_LF__DOT__ProofObjects_LF_ProofObjects_eq {X : Type} : X → X → Prop where
  | eq_refl : ∀ (x : X), Original_LF__DOT__ProofObjects_LF_ProofObjects_eq x x

-- eq_add
def Original_LF__DOT__ProofObjects_LF_ProofObjects_eq__add 
  (n1 n2 : nat) (Heq : Original_LF__DOT__ProofObjects_LF_ProofObjects_eq n1 n2) : 
    Original_LF__DOT__ProofObjects_LF_ProofObjects_eq (nat.S n1) (nat.S n2) :=
  @Original_LF__DOT__ProofObjects_LF_ProofObjects_eq.rec nat n1 
    (fun y _ => Original_LF__DOT__ProofObjects_LF_ProofObjects_eq (nat.S n1) (nat.S y))
    (Original_LF__DOT__ProofObjects_LF_ProofObjects_eq.eq_refl (nat.S n1))
    n2 Heq

-- ProofObjects.Props.or
inductive Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or (P Q : Prop) : Prop where
  | or_introl : P → Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or P Q
  | or_intror : Q → Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or P Q

-- or_commut' (Admitted)
axiom Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or__commut' : 
  ∀ (P Q : Prop), Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or P Q → 
                  Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or Q P

-- ============================================================
-- Original.LF_DOT_Basics.leb
-- ============================================================

def Original_LF__DOT__Basics_LF_Basics_leb : nat → nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O, _ => Original_LF__DOT__Basics_LF_Basics_bool.true
  | nat.S _, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S n', nat.S m' => Original_LF__DOT__Basics_LF_Basics_leb n' m'

-- ============================================================
-- Original.LF_DOT_IndProp.LePlayground.le
-- ============================================================

inductive Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le : nat → nat → Prop where
  | le_n (n : nat) : Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le n n
  | le_S (n m : nat) : Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le n m → Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le n (nat.S m)

-- le_inversion (Admitted)
axiom Original_LF__DOT__IndProp_LF_IndProp_le__inversion :
  ∀ (n m : nat),
    Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le n m →
    or (@Corelib_Init_Logic_eq nat n m)
       (ex (fun m' : nat => and (@Corelib_Init_Logic_eq nat m (nat.S m')) (Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le n m')))

-- leb_true_trans (Admitted)
axiom Original_LF__DOT__IndProp_LF_IndProp_leb__true__trans :
  ∀ (n m o : nat),
    @Corelib_Init_Logic_eq Original_LF__DOT__Basics_LF_Basics_bool (Original_LF__DOT__Basics_LF_Basics_leb n m) Original_LF__DOT__Basics_LF_Basics_bool.true →
    @Corelib_Init_Logic_eq Original_LF__DOT__Basics_LF_Basics_bool (Original_LF__DOT__Basics_LF_Basics_leb m o) Original_LF__DOT__Basics_LF_Basics_bool.true →
    @Corelib_Init_Logic_eq Original_LF__DOT__Basics_LF_Basics_bool (Original_LF__DOT__Basics_LF_Basics_leb n o) Original_LF__DOT__Basics_LF_Basics_bool.true

-- ============================================================
-- Original.LF_DOT_IndProp.re_not_empty
-- ============================================================

-- Local andb and orb for Original_LF__DOT__Basics_LF_Basics_bool
def Original_andb : Original_LF__DOT__Basics_LF_Basics_bool → Original_LF__DOT__Basics_LF_Basics_bool → Original_LF__DOT__Basics_LF_Basics_bool
  | Original_LF__DOT__Basics_LF_Basics_bool.true, b => b
  | Original_LF__DOT__Basics_LF_Basics_bool.false, _ => Original_LF__DOT__Basics_LF_Basics_bool.false

def Original_orb : Original_LF__DOT__Basics_LF_Basics_bool → Original_LF__DOT__Basics_LF_Basics_bool → Original_LF__DOT__Basics_LF_Basics_bool
  | Original_LF__DOT__Basics_LF_Basics_bool.true, _ => Original_LF__DOT__Basics_LF_Basics_bool.true
  | Original_LF__DOT__Basics_LF_Basics_bool.false, b => b

def Original_LF__DOT__IndProp_LF_IndProp_re__not__empty {T : Type} : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__Basics_LF_Basics_bool
  | Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptySet => Original_LF__DOT__Basics_LF_Basics_bool.false
  | Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptyStr => Original_LF__DOT__Basics_LF_Basics_bool.true
  | Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Char _ => Original_LF__DOT__Basics_LF_Basics_bool.true
  | Original_LF__DOT__IndProp_LF_IndProp_reg__exp.App re1 re2 => Original_andb (Original_LF__DOT__IndProp_LF_IndProp_re__not__empty re1) (Original_LF__DOT__IndProp_LF_IndProp_re__not__empty re2)
  | Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Union re1 re2 => Original_orb (Original_LF__DOT__IndProp_LF_IndProp_re__not__empty re1) (Original_LF__DOT__IndProp_LF_IndProp_re__not__empty re2)
  | Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star _ => Original_LF__DOT__Basics_LF_Basics_bool.true

-- re_not_empty_correct (Admitted)
axiom Original_LF__DOT__IndProp_LF_IndProp_re__not__empty__correct :
  ∀ (T : Type) (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T),
    iff 
      (ex (fun s : Original_LF__DOT__Poly_LF_Poly_list T => Original_LF__DOT__IndProp_LF_IndProp_exp__match s re))
      (@Corelib_Init_Logic_eq Original_LF__DOT__Basics_LF_Basics_bool 
        (@Original_LF__DOT__IndProp_LF_IndProp_re__not__empty T re) 
        Original_LF__DOT__Basics_LF_Basics_bool.true)

-- ============================================================
-- Original.LF_DOT_Logic.add_comm3_take2 (Admitted)
-- ============================================================

axiom Original_LF__DOT__Logic_LF_Logic_add__comm3__take2 :
  ∀ (n m p : nat),
    @Corelib_Init_Logic_eq nat (Nat_add n (Nat_add m p)) (Nat_add (Nat_add p m) n)

-- ============================================================
-- Original.LF_DOT_IndPrinciples definitions
-- ============================================================

-- natlist' (same as natlist but in IndPrinciples module)
inductive Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist' : Type where
  | nnil' : Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist'
  | nsnoc : Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist' → nat → Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist'

-- add_comm'' (Admitted)
axiom Original_LF__DOT__IndPrinciples_LF_IndPrinciples_add__comm'' :
  ∀ (n m : nat),
    @Corelib_Init_Logic_eq nat (Nat_add n m) (Nat_add m n)

-- ============================================================
-- Original.LF_DOT_IndProp.EvPlayground.ev (moved before AltAuto)
-- ============================================================

inductive Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev : nat → Prop where
  | ev_0 : Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev nat.O
  | ev_SS : (n : nat) → Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev n → Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev (nat.S (nat.S n))

-- ============================================================
-- Original.LF_DOT_AltAuto.match_ex2 (Admitted)
-- ============================================================

-- match_ex2 : True /\ True (Admitted)
axiom Original_LF__DOT__AltAuto_LF_AltAuto_match__ex2 : and MyTrue MyTrue

-- add_assoc'' : forall n m p : nat, n + (m + p) = (n + m) + p (Admitted)
axiom Original_LF__DOT__AltAuto_LF_AltAuto_add__assoc'' :
  ∀ (n m p : nat), @Corelib_Init_Logic_eq nat (Nat_add n (Nat_add m p)) (Nat_add (Nat_add n m) p)

-- add_assoc : same as add_assoc'' (Admitted)
axiom Original_LF__DOT__AltAuto_LF_AltAuto_add__assoc :
  ∀ (n m p : nat), @Corelib_Init_Logic_eq nat (Nat_add n (Nat_add m p)) (Nat_add (Nat_add n m) p)

-- ev100 : ev 100 (Admitted)
axiom Original_LF__DOT__AltAuto_LF_AltAuto_ev100 :
  Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- plus_n_Sm : forall n m, S (n + m) = n + S m (Admitted)
axiom Original_LF__DOT__AltAuto_LF_AltAuto_plus__n__Sm :
  ∀ (n m : nat), @Corelib_Init_Logic_eq nat (nat.S (Nat_add n m)) (Nat_add n (nat.S m))

-- sat_ex1 : 1 + 1 = 2 (Admitted)
axiom Original_LF__DOT__AltAuto_LF_AltAuto_sat__ex1 : @Corelib_Init_Logic_eq nat (Nat_add (nat.S nat.O) (nat.S nat.O)) (nat.S (nat.S nat.O))

-- ============================================================
-- Basics theorems
-- ============================================================

-- mult_n_1 : forall p, p * 1 = p (Admitted)
axiom Original_LF__DOT__Basics_LF_Basics_mult__n__1 :
  ∀ (p : nat), @Corelib_Init_Logic_eq nat (Nat_mul p (nat.S nat.O)) p

-- ============================================================
-- Induction theorems
-- ============================================================

-- mul_0_r : forall n, n * 0 = 0 (Admitted)
axiom Original_LF__DOT__Induction_LF_Induction_mul__0__r :
  ∀ (n : nat), @Corelib_Init_Logic_eq nat (Nat_mul n nat.O) nat.O

-- ============================================================
-- Logic theorems
-- ============================================================

-- and_example : 3 + 4 = 7 /\ 2 * 2 = 4 (Admitted)
axiom Original_LF__DOT__Logic_LF_Logic_and__example :
  and (@Corelib_Init_Logic_eq nat (Nat_add (nat.S (nat.S (nat.S nat.O))) (nat.S (nat.S (nat.S (nat.S nat.O))))) (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))))))
      (@Corelib_Init_Logic_eq nat (Nat_mul (nat.S (nat.S nat.O)) (nat.S (nat.S nat.O))) (nat.S (nat.S (nat.S (nat.S nat.O)))))

-- iff_refl : forall P, P <-> P (Admitted)
axiom Original_LF__DOT__Logic_LF_Logic_iff__refl :
  ∀ (P : Prop), iff P P

-- mul_eq_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0 (Admitted)
axiom Original_LF__DOT__Logic_LF_Logic_mul__eq__0 :
  ∀ (n m : nat), iff (@Corelib_Init_Logic_eq nat (Nat_mul n m) nat.O)
                     (or (@Corelib_Init_Logic_eq nat n nat.O) (@Corelib_Init_Logic_eq nat m nat.O))

-- or_distributes_over_and : forall P Q R, P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R) (Admitted)
axiom Original_LF__DOT__Logic_LF_Logic_or__distributes__over__and :
  ∀ (P Q R : Prop), iff (or P (and Q R)) (and (or P Q) (or P R))

-- consequentia_mirabilis : forall P : Prop, (~P -> P) -> P
-- This is a type/proposition, not a term
def Original_LF__DOT__Logic_LF_Logic_consequentia__mirabilis : Prop :=
  ∀ (P : Prop), (Logic_not P → P) → P

-- ============================================================
-- IndProp theorems
-- ============================================================

-- ev_inversion : forall n, ev n -> n = 0 \/ exists n', n = S (S n') /\ ev n' (Admitted)
axiom Original_LF__DOT__IndProp_LF_IndProp_ev__inversion :
  ∀ (n : nat), Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev n →
    or (@Corelib_Init_Logic_eq nat n nat.O)
       (ex (fun n' : nat => and (@Corelib_Init_Logic_eq nat n (nat.S (nat.S n')))
                                (Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev n')))

-- ev5_nonsense : ev 5 -> 2 + 2 = 9 (Admitted)
axiom Original_LF__DOT__IndProp_LF_IndProp_ev5__nonsense :
  Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))) →
    @Corelib_Init_Logic_eq nat (Nat_add (nat.S (nat.S nat.O)) (nat.S (nat.S nat.O))) (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))))))

-- ============================================================
-- Imp theorems
-- ============================================================

-- aevalR_extended.aevalR : relation on aexp and nat (Admitted)
-- This is the evaluation relation for the extended aexp type

-- ============================================================
-- Original.LF_DOT_Imp.aevalR_extended.aexp
-- ============================================================

inductive Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp : Type where
  | AAny : Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp
  | ANum : nat → Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp
  | APlus : Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp → Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp → Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp
  | AMinus : Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp → Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp → Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp
  | AMult : Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp → Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp → Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp

-- ============================================================
-- Original.LF_DOT_Imp.aevalR_extended.aevalR
-- ============================================================

inductive Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR : Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp → nat → Prop where
  | E_Any (n : nat) : Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp.AAny n
  | E_ANum (n : nat) : Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR (Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp.ANum n) n
  | E_APlus (a1 a2 : Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp) (n1 n2 : nat) :
      Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR a1 n1 →
      Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR a2 n2 →
      Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR (Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp.APlus a1 a2) (Nat_add n1 n2)
  | E_AMinus (a1 a2 : Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp) (n1 n2 : nat) :
      Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR a1 n1 →
      Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR a2 n2 →
      Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR (Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp.AMinus a1 a2) (Nat_sub n1 n2)
  | E_AMult (a1 a2 : Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp) (n1 n2 : nat) :
      Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR a1 n1 →
      Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR a2 n2 →
      Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR (Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp.AMult a1 a2) (Nat_mul n1 n2)


