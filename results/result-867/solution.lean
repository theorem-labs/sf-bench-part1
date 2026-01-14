-- Comprehensive Lean translation for all isomorphism proofs
-- Combines definitions from multiple reference solutions

set_option linter.all false

-- ============================================================================
-- Basic Types
-- ============================================================================

-- Define our own bool type with names that won't conflict  
inductive mybool : Type where
  | mytrue : mybool
  | myfalse : mybool

-- Aliases for bool (using different names to avoid conflict with Lean's Bool)
def mybool2 := mybool
def bool_true := mybool.mytrue
def bool_false := mybool.myfalse
def mybool_mytrue := mybool.mytrue
def mybool_myfalse := mybool.myfalse
-- For the checker: Imported.bool -> mybool
def mybool_alias := mybool

-- Define our own nat type
inductive nat : Type where
  | O : nat
  | S : nat → nat

-- Aliases that will become Imported.nat, etc.
def nat_O := nat.O
def nat_S := nat.S
def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Additional aliases for isomorphisms
def true := mybool.mytrue
def false := mybool.myfalse

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

-- Define equality on bools
def bool_eqb : mybool → mybool → mybool
  | mybool.mytrue, mybool.mytrue => mybool.mytrue
  | mybool.myfalse, mybool.myfalse => mybool.mytrue
  | _, _ => mybool.myfalse

-- ============================================================================
-- Ascii and String Types
-- ============================================================================

-- Define Ascii as 8 bools (like Rocq's Ascii.ascii)
inductive Ascii : Type where
  | Ascii : mybool → mybool → mybool → mybool → mybool → mybool → mybool → mybool → Ascii

-- Aliases expected by Rocq isomorphisms
def Ascii_ascii := Ascii
def Ascii_Ascii := Ascii.Ascii
def Ascii_ascii_Ascii := Ascii.Ascii

-- Define equality on Ascii
def Ascii_eqb : Ascii → Ascii → mybool
  | Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7, Ascii.Ascii c0 c1 c2 c3 c4 c5 c6 c7 =>
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
  | String : Ascii → String_string → String_string

-- String aliases for isomorphisms
def String_string_EmptyString := String_string.EmptyString
def String_string_String := String_string.String
def String_EmptyString := String_string.EmptyString
def String_String := String_string.String

-- String equality
def String_eqb : String_string → String_string → mybool
  | String_string.EmptyString, String_string.EmptyString => mybool.mytrue
  | String_string.String c1 s1, String_string.String c2 s2 =>
    bool_andb (Ascii_eqb c1 c2) (String_eqb s1 s2)
  | _, _ => mybool.myfalse

-- ============================================================================
-- Maps
-- ============================================================================

-- total_map type (function from string to A)
def Original_LF__DOT__Maps_LF_Maps_total__map (A : Type) := String_string → A

-- t_empty: create empty total map with default value
def Original_LF__DOT__Maps_LF_Maps_t__empty {A : Type} (v : A) : Original_LF__DOT__Maps_LF_Maps_total__map A :=
  fun _ => v

-- t_update function
def Original_LF__DOT__Maps_LF_Maps_t__update {A : Type} (m : Original_LF__DOT__Maps_LF_Maps_total__map A)
    (x : String_string) (v : A) : Original_LF__DOT__Maps_LF_Maps_total__map A :=
  fun x' => match String_eqb x x' with
    | mybool.mytrue => v
    | mybool.myfalse => m x'

-- ============================================================================
-- Imp Language
-- ============================================================================

-- State is total_map nat
def Original_LF__DOT__Imp_LF_Imp_state := Original_LF__DOT__Maps_LF_Maps_total__map nat

-- Helper for building ASCII characters
-- 'X' = 88 = 0b01011000, LSB first: 0,0,0,1,1,0,1,0
def charX : Ascii := Ascii.Ascii mybool.myfalse mybool.myfalse mybool.myfalse mybool.mytrue mybool.mytrue mybool.myfalse mybool.mytrue mybool.myfalse
-- 'Y' = 89 = 0b01011001, LSB first: 1,0,0,1,1,0,1,0
def charY : Ascii := Ascii.Ascii mybool.mytrue mybool.myfalse mybool.myfalse mybool.mytrue mybool.mytrue mybool.myfalse mybool.mytrue mybool.myfalse
-- 'Z' = 90 = 0b01011010, LSB first: 0,1,0,1,1,0,1,0
def charZ : Ascii := Ascii.Ascii mybool.myfalse mybool.mytrue mybool.myfalse mybool.mytrue mybool.mytrue mybool.myfalse mybool.mytrue mybool.myfalse

-- Variables X, Y, Z
def Original_LF__DOT__Imp_LF_Imp_X : String_string := String_string.String charX String_string.EmptyString
def Original_LF__DOT__Imp_LF_Imp_Y : String_string := String_string.String charY String_string.EmptyString
def Original_LF__DOT__Imp_LF_Imp_Z : String_string := String_string.String charZ String_string.EmptyString

-- Arithmetic expressions (matches Original.LF_DOT_Imp.LF.Imp.aexp)
inductive Original_LF__DOT__Imp_LF_Imp_aexp : Type where
  | ANum : nat → Original_LF__DOT__Imp_LF_Imp_aexp
  | AId : String_string → Original_LF__DOT__Imp_LF_Imp_aexp
  | APlus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp
  | AMinus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp
  | AMult : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp

-- Constructor aliases for aexp
def Original_LF__DOT__Imp_LF_Imp_ANum := Original_LF__DOT__Imp_LF_Imp_aexp.ANum
def Original_LF__DOT__Imp_LF_Imp_AId := Original_LF__DOT__Imp_LF_Imp_aexp.AId
def Original_LF__DOT__Imp_LF_Imp_APlus := Original_LF__DOT__Imp_LF_Imp_aexp.APlus
def Original_LF__DOT__Imp_LF_Imp_AMinus := Original_LF__DOT__Imp_LF_Imp_aexp.AMinus
def Original_LF__DOT__Imp_LF_Imp_AMult := Original_LF__DOT__Imp_LF_Imp_aexp.AMult

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

-- Constructor aliases for bexp
def Original_LF__DOT__Imp_LF_Imp_BTrue := Original_LF__DOT__Imp_LF_Imp_bexp.BTrue
def Original_LF__DOT__Imp_LF_Imp_BFalse := Original_LF__DOT__Imp_LF_Imp_bexp.BFalse
def Original_LF__DOT__Imp_LF_Imp_BEq := Original_LF__DOT__Imp_LF_Imp_bexp.BEq
def Original_LF__DOT__Imp_LF_Imp_BNeq := Original_LF__DOT__Imp_LF_Imp_bexp.BNeq
def Original_LF__DOT__Imp_LF_Imp_BLe := Original_LF__DOT__Imp_LF_Imp_bexp.BLe
def Original_LF__DOT__Imp_LF_Imp_BGt := Original_LF__DOT__Imp_LF_Imp_bexp.BGt
def Original_LF__DOT__Imp_LF_Imp_BNot := Original_LF__DOT__Imp_LF_Imp_bexp.BNot
def Original_LF__DOT__Imp_LF_Imp_BAnd := Original_LF__DOT__Imp_LF_Imp_bexp.BAnd

-- Commands (matches Original.LF_DOT_Imp.LF.Imp.com)
inductive Original_LF__DOT__Imp_LF_Imp_com : Type where
  | CSkip : Original_LF__DOT__Imp_LF_Imp_com
  | CAsgn : String_string → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_com
  | CSeq : Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com
  | CIf : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com
  | CWhile : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com

-- Constructor aliases for the checkers
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

-- ============================================================================
-- Propositional Types
-- ============================================================================

-- True type as Prop (will be exported as SProp in Rocq)
inductive TrueType : Prop
| I : TrueType

def TrueType_I : TrueType := TrueType.I
-- Aliases for True (True is reserved in Lean)
def myTrue := TrueType
def myTrue_I := TrueType.I

-- False type (as Prop - will export to SProp in Rocq)
inductive MyFalse : Prop where

-- Alias for False (False is reserved in Lean)
def myFalse := MyFalse

-- Equality type in Prop (will become SProp in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} (a : A) : A → Prop
| refl : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl

-- Equality for SProp (needed for the Prop version)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} (a : A) : A → Prop
| refl : Corelib_Init_Logic_eq_Prop a a

def Corelib_Init_Logic_eq_Prop_refl {A : Prop} (a : A) : Corelib_Init_Logic_eq_Prop a a :=
  Corelib_Init_Logic_eq_Prop.refl

-- Generic MyEq type (just another equality type, named to avoid conflict with Lean's Eq)
inductive MyEq {A : Type} (a : A) : A → Prop
| refl : MyEq a a

def MyEq_refl {A : Type} (a : A) : MyEq a a := MyEq.refl

-- Existential type in Prop
inductive ex {α : Type} (P : α → Prop) : Prop where
  | intro (w : α) (h : P w) : ex P

-- Iff type
structure iff (a b : Prop) : Prop where
  intro ::
  mp : a → b
  mpr : b → a

-- ============================================================================
-- List Types (from LF.Poly)
-- ============================================================================

-- Polymorphic list type matching Original.LF_DOT_Poly.LF.Poly.list
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

-- List constructors as explicit definitions
def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

def Original_LF__DOT__Poly_LF_Poly_cons (X : Type) : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons

-- app function for lists
def Original_LF__DOT__Poly_LF_Poly_app (X : Type) (l1 l2 : Original_LF__DOT__Poly_LF_Poly_list X) : Original_LF__DOT__Poly_LF_Poly_list X :=
  match l1 with
  | Original_LF__DOT__Poly_LF_Poly_list.nil => l2
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t => Original_LF__DOT__Poly_LF_Poly_list.cons h (Original_LF__DOT__Poly_LF_Poly_app X t l2)

-- Standard Coq list type
inductive list (A : Type) : Type where
  | nil : list A
  | cons : A → list A → list A

-- Export constructors for list
def list_nil (A : Type) : list A := list.nil
def list_cons (A : Type) (h : A) (t : list A) : list A := list.cons h t

-- ============================================================================
-- Regular Expressions (from LF.IndProp)
-- ============================================================================

-- Regular expression type
inductive Original_LF__DOT__IndProp_LF_IndProp_reg__exp (T : Type) : Type where
  | EmptySet : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | EmptyStr : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Char : T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | App : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Union : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Star : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T

-- Constructor definitions for reg_exp
def Original_LF__DOT__IndProp_LF_IndProp_EmptySet (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  .EmptySet

def Original_LF__DOT__IndProp_LF_IndProp_EmptyStr (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  .EmptyStr

def Original_LF__DOT__IndProp_LF_IndProp_Char (T : Type) : T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  .Char

def Original_LF__DOT__IndProp_LF_IndProp_App (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  .App

def Original_LF__DOT__IndProp_LF_IndProp_Union (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  .Union

def Original_LF__DOT__IndProp_LF_IndProp_Star (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  .Star

-- exp_match inductive type (s =~ re)
inductive Original_LF__DOT__IndProp_LF_IndProp_exp__match {T : Type} : 
    Original_LF__DOT__Poly_LF_Poly_list T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Prop where
  | MEmpty : Original_LF__DOT__IndProp_LF_IndProp_exp__match .nil .EmptyStr
  | MChar (x : T) : Original_LF__DOT__IndProp_LF_IndProp_exp__match (.cons x .nil) (.Char x)
  | MApp (s1 : Original_LF__DOT__Poly_LF_Poly_list T) (re1 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
         (s2 : Original_LF__DOT__Poly_LF_Poly_list T) (re2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
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

-- ============================================================================
-- LF.Basics Types
-- ============================================================================

-- Boolean type (matching LF.Basics.bool)
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | Original_LF__DOT__Basics_LF_Basics_bool_true : Original_LF__DOT__Basics_LF_Basics_bool
  | Original_LF__DOT__Basics_LF_Basics_bool_false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.Original_LF__DOT__Basics_LF_Basics_bool_true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.Original_LF__DOT__Basics_LF_Basics_bool_false

-- ============================================================================
-- Imp Semantics (ceval)
-- ============================================================================

-- empty_st: the empty state that maps everything to 0
def Original_LF__DOT__Imp_LF_Imp_empty__st : Original_LF__DOT__Imp_LF_Imp_state :=
  Original_LF__DOT__Maps_LF_Maps_t__empty nat.O

-- ceval: big-step operational semantics for Imp
inductive Original_LF__DOT__Imp_LF_Imp_ceval : Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_state → Original_LF__DOT__Imp_LF_Imp_state → Prop where
  | E_Skip : ∀ (st : Original_LF__DOT__Imp_LF_Imp_state),
      Original_LF__DOT__Imp_LF_Imp_ceval .CSkip st st
  | E_Asgn : ∀ (st : Original_LF__DOT__Imp_LF_Imp_state) (a : Original_LF__DOT__Imp_LF_Imp_aexp) (n : nat) (x : String_string),
      Original_LF__DOT__Imp_LF_Imp_aeval st a = n →
      Original_LF__DOT__Imp_LF_Imp_ceval (.CAsgn x a) st (Original_LF__DOT__Maps_LF_Maps_t__update st x n)
  | E_Seq : ∀ (c1 c2 : Original_LF__DOT__Imp_LF_Imp_com) (st st' st'' : Original_LF__DOT__Imp_LF_Imp_state),
      Original_LF__DOT__Imp_LF_Imp_ceval c1 st st' →
      Original_LF__DOT__Imp_LF_Imp_ceval c2 st' st'' →
      Original_LF__DOT__Imp_LF_Imp_ceval (.CSeq c1 c2) st st''
  | E_IfTrue : ∀ (st st' : Original_LF__DOT__Imp_LF_Imp_state) (b : Original_LF__DOT__Imp_LF_Imp_bexp) (c1 c2 : Original_LF__DOT__Imp_LF_Imp_com),
      Original_LF__DOT__Imp_LF_Imp_beval st b = mybool.mytrue →
      Original_LF__DOT__Imp_LF_Imp_ceval c1 st st' →
      Original_LF__DOT__Imp_LF_Imp_ceval (.CIf b c1 c2) st st'
  | E_IfFalse : ∀ (st st' : Original_LF__DOT__Imp_LF_Imp_state) (b : Original_LF__DOT__Imp_LF_Imp_bexp) (c1 c2 : Original_LF__DOT__Imp_LF_Imp_com),
      Original_LF__DOT__Imp_LF_Imp_beval st b = mybool.myfalse →
      Original_LF__DOT__Imp_LF_Imp_ceval c2 st st' →
      Original_LF__DOT__Imp_LF_Imp_ceval (.CIf b c1 c2) st st'
  | E_WhileFalse : ∀ (b : Original_LF__DOT__Imp_LF_Imp_bexp) (st : Original_LF__DOT__Imp_LF_Imp_state) (c : Original_LF__DOT__Imp_LF_Imp_com),
      Original_LF__DOT__Imp_LF_Imp_beval st b = mybool.myfalse →
      Original_LF__DOT__Imp_LF_Imp_ceval (.CWhile b c) st st
  | E_WhileTrue : ∀ (st st' st'' : Original_LF__DOT__Imp_LF_Imp_state) (b : Original_LF__DOT__Imp_LF_Imp_bexp) (c : Original_LF__DOT__Imp_LF_Imp_com),
      Original_LF__DOT__Imp_LF_Imp_beval st b = mybool.mytrue →
      Original_LF__DOT__Imp_LF_Imp_ceval c st st' →
      Original_LF__DOT__Imp_LF_Imp_ceval (.CWhile b c) st' st'' →
      Original_LF__DOT__Imp_LF_Imp_ceval (.CWhile b c) st st''

-- ceval constructor aliases
def Original_LF__DOT__Imp_LF_Imp_ceval_E__Skip := @Original_LF__DOT__Imp_LF_Imp_ceval.E_Skip
def Original_LF__DOT__Imp_LF_Imp_ceval_E__Asgn := @Original_LF__DOT__Imp_LF_Imp_ceval.E_Asgn
def Original_LF__DOT__Imp_LF_Imp_ceval_E__Seq := @Original_LF__DOT__Imp_LF_Imp_ceval.E_Seq
def Original_LF__DOT__Imp_LF_Imp_ceval_E__IfTrue := @Original_LF__DOT__Imp_LF_Imp_ceval.E_IfTrue
def Original_LF__DOT__Imp_LF_Imp_ceval_E__IfFalse := @Original_LF__DOT__Imp_LF_Imp_ceval.E_IfFalse
def Original_LF__DOT__Imp_LF_Imp_ceval_E__WhileFalse := @Original_LF__DOT__Imp_LF_Imp_ceval.E_WhileFalse
def Original_LF__DOT__Imp_LF_Imp_ceval_E__WhileTrue := @Original_LF__DOT__Imp_LF_Imp_ceval.E_WhileTrue

-- ceval_example1: empty_st =[ X := 2; if (X <= 1) then Y := 3 else Z := 4 end ]=> (Z !-> 4 ; X !-> 2)
-- This is admitted in the original, so we use an axiom
axiom Original_LF__DOT__Imp_LF_Imp_ceval__example1 :
  Original_LF__DOT__Imp_LF_Imp_ceval
    (.CSeq
      (.CAsgn Original_LF__DOT__Imp_LF_Imp_X (.ANum (nat.S (nat.S nat.O))))
      (.CIf
        (.BLe (.AId Original_LF__DOT__Imp_LF_Imp_X) (.ANum (nat.S nat.O)))
        (.CAsgn Original_LF__DOT__Imp_LF_Imp_Y (.ANum (nat.S (nat.S (nat.S nat.O)))))
        (.CAsgn Original_LF__DOT__Imp_LF_Imp_Z (.ANum (nat.S (nat.S (nat.S (nat.S nat.O))))))))
    Original_LF__DOT__Imp_LF_Imp_empty__st
    (Original_LF__DOT__Maps_LF_Maps_t__update
      (Original_LF__DOT__Maps_LF_Maps_t__update Original_LF__DOT__Imp_LF_Imp_empty__st Original_LF__DOT__Imp_LF_Imp_X (nat.S (nat.S nat.O)))
      Original_LF__DOT__Imp_LF_Imp_Z (nat.S (nat.S (nat.S (nat.S nat.O)))))

-- ceval_example2: empty_st =[ X := 0; Y := 1; Z := 2 ]=> (Z !-> 2 ; Y !-> 1 ; X !-> 0)
-- This is admitted in the original, so we use an axiom
axiom Original_LF__DOT__Imp_LF_Imp_ceval__example2 :
  Original_LF__DOT__Imp_LF_Imp_ceval
    (.CSeq
      (.CAsgn Original_LF__DOT__Imp_LF_Imp_X (.ANum nat.O))
      (.CSeq
        (.CAsgn Original_LF__DOT__Imp_LF_Imp_Y (.ANum (nat.S nat.O)))
        (.CAsgn Original_LF__DOT__Imp_LF_Imp_Z (.ANum (nat.S (nat.S nat.O))))))
    Original_LF__DOT__Imp_LF_Imp_empty__st
    (Original_LF__DOT__Maps_LF_Maps_t__update
      (Original_LF__DOT__Maps_LF_Maps_t__update
        (Original_LF__DOT__Maps_LF_Maps_t__update Original_LF__DOT__Imp_LF_Imp_empty__st Original_LF__DOT__Imp_LF_Imp_X nat.O)
        Original_LF__DOT__Imp_LF_Imp_Y (nat.S nat.O))
      Original_LF__DOT__Imp_LF_Imp_Z (nat.S (nat.S nat.O)))
