-- Comprehensive Lean 4 translation combining all needed definitions
-- This merges definitions from multiple reference solutions

set_option linter.unusedVariables false
set_option autoImplicit false

-- ================================================================
-- Basic types
-- ================================================================

-- Natural numbers (matching Rocq's nat)
inductive nat : Type
| O : nat
| S : nat → nat

-- Aliases for constructors
def _0 : nat := nat.O
def S' : nat → nat := nat.S
def S_alias : nat → nat := nat.S

-- Addition on nat
def Nat_add : nat → nat → nat
| nat.O, m => m
| nat.S p, m => nat.S (Nat_add p m)

-- Multiplication on nat
def Nat_mul : nat → nat → nat
| nat.O, _ => nat.O
| nat.S n', m => Nat_add m (Nat_mul n' m)

-- Subtraction on nat
def Nat_sub : nat → nat → nat
| nat.O, _ => nat.O
| n, nat.O => n
| nat.S n', nat.S m' => Nat_sub n' m'

-- Predecessor
def Nat_pred : nat → nat
| nat.O => nat.O
| nat.S n' => n'

-- Boolean type (matching Rocq bool - using mybool to avoid clash with Lean's Bool)
inductive mybool : Type
| mytrue : mybool
| myfalse : mybool

-- Aliases
def mytrue : mybool := mybool.mytrue
def myfalse : mybool := mybool.myfalse

-- ================================================================
-- LF Basics types
-- ================================================================

-- Boolean type (matching LF.Basics.bool)
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type
| true : Original_LF__DOT__Basics_LF_Basics_bool
| false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- negb
def Original_LF__DOT__Basics_LF_Basics_negb (b : Original_LF__DOT__Basics_LF_Basics_bool) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match b with
  | Original_LF__DOT__Basics_LF_Basics_bool.true => Original_LF__DOT__Basics_LF_Basics_bool.false
  | Original_LF__DOT__Basics_LF_Basics_bool.false => Original_LF__DOT__Basics_LF_Basics_bool.true

-- andb
def Original_LF__DOT__Basics_LF_Basics_andb (b1 b2 : Original_LF__DOT__Basics_LF_Basics_bool) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match b1 with
  | Original_LF__DOT__Basics_LF_Basics_bool.true => b2
  | Original_LF__DOT__Basics_LF_Basics_bool.false => Original_LF__DOT__Basics_LF_Basics_bool.false

-- orb
def Original_LF__DOT__Basics_LF_Basics_orb (b1 b2 : Original_LF__DOT__Basics_LF_Basics_bool) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match b1 with
  | Original_LF__DOT__Basics_LF_Basics_bool.true => Original_LF__DOT__Basics_LF_Basics_bool.true
  | Original_LF__DOT__Basics_LF_Basics_bool.false => b2

-- eqb
def Original_LF__DOT__Basics_LF_Basics_eqb : nat → nat → Original_LF__DOT__Basics_LF_Basics_bool
| nat.O, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.true
| nat.O, nat.S _ => Original_LF__DOT__Basics_LF_Basics_bool.false
| nat.S _, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
| nat.S n', nat.S m' => Original_LF__DOT__Basics_LF_Basics_eqb n' m'

-- leb
def Original_LF__DOT__Basics_LF_Basics_leb : nat → nat → Original_LF__DOT__Basics_LF_Basics_bool
| nat.O, _ => Original_LF__DOT__Basics_LF_Basics_bool.true
| nat.S _, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
| nat.S n', nat.S m' => Original_LF__DOT__Basics_LF_Basics_leb n' m'

-- even - standalone implementation using double recursion
def Original_LF__DOT__Basics_LF_Basics_even : nat → Original_LF__DOT__Basics_LF_Basics_bool
| nat.O => Original_LF__DOT__Basics_LF_Basics_bool.true
| nat.S nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
| nat.S (nat.S n') => Original_LF__DOT__Basics_LF_Basics_even n'

-- odd
def Original_LF__DOT__Basics_LF_Basics_odd (n : nat) : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_negb (Original_LF__DOT__Basics_LF_Basics_even n)

-- letter
inductive Original_LF__DOT__Basics_LF_Basics_letter : Type
| A : Original_LF__DOT__Basics_LF_Basics_letter
| B : Original_LF__DOT__Basics_LF_Basics_letter
| C : Original_LF__DOT__Basics_LF_Basics_letter
| D : Original_LF__DOT__Basics_LF_Basics_letter
| F : Original_LF__DOT__Basics_LF_Basics_letter

-- modifier
inductive Original_LF__DOT__Basics_LF_Basics_modifier : Type
| Plus : Original_LF__DOT__Basics_LF_Basics_modifier
| Natural : Original_LF__DOT__Basics_LF_Basics_modifier
| Minus : Original_LF__DOT__Basics_LF_Basics_modifier

-- grade
inductive Original_LF__DOT__Basics_LF_Basics_grade : Type
| Grade : Original_LF__DOT__Basics_LF_Basics_letter → Original_LF__DOT__Basics_LF_Basics_modifier → Original_LF__DOT__Basics_LF_Basics_grade

-- Bool negation
def negb : mybool → mybool
| mybool.mytrue => mybool.myfalse
| mybool.myfalse => mybool.mytrue

-- Bool conjunction
def andb : mybool → mybool → mybool
| mybool.mytrue, b2 => b2
| mybool.myfalse, _ => mybool.myfalse

-- Bool disjunction
def orb : mybool → mybool → mybool
| mybool.mytrue, _ => mybool.mytrue
| mybool.myfalse, b2 => b2

-- Nat equality
def nat_eqb : nat → nat → mybool
| nat.O, nat.O => mybool.mytrue
| nat.O, nat.S _ => mybool.myfalse
| nat.S _, nat.O => mybool.myfalse
| nat.S n', nat.S m' => nat_eqb n' m'

-- Nat less than or equal
def nat_leb : nat → nat → mybool
| nat.O, _ => mybool.mytrue
| nat.S _, nat.O => mybool.myfalse
| nat.S n', nat.S m' => nat_leb n' m'

-- ================================================================
-- Ascii and String
-- ================================================================

-- Ascii type
inductive Ascii_ascii : Type
| Ascii : mybool → mybool → mybool → mybool → mybool → mybool → mybool → mybool → Ascii_ascii

-- String type
inductive String_string : Type
| EmptyString : String_string
| String : Ascii_ascii → String_string → String_string

-- String equality
def mybool_eqb : mybool → mybool → mybool
| mybool.mytrue, mybool.mytrue => mybool.mytrue
| mybool.myfalse, mybool.myfalse => mybool.mytrue
| _, _ => mybool.myfalse

def Ascii_eqb : Ascii_ascii → Ascii_ascii → mybool
| Ascii_ascii.Ascii b1 b2 b3 b4 b5 b6 b7 b8, Ascii_ascii.Ascii c1 c2 c3 c4 c5 c6 c7 c8 =>
  match mybool_eqb b1 c1 with
  | mybool.myfalse => mybool.myfalse
  | mybool.mytrue =>
    match mybool_eqb b2 c2 with
    | mybool.myfalse => mybool.myfalse
    | mybool.mytrue =>
      match mybool_eqb b3 c3 with
      | mybool.myfalse => mybool.myfalse
      | mybool.mytrue =>
        match mybool_eqb b4 c4 with
        | mybool.myfalse => mybool.myfalse
        | mybool.mytrue =>
          match mybool_eqb b5 c5 with
          | mybool.myfalse => mybool.myfalse
          | mybool.mytrue =>
            match mybool_eqb b6 c6 with
            | mybool.myfalse => mybool.myfalse
            | mybool.mytrue =>
              match mybool_eqb b7 c7 with
              | mybool.myfalse => mybool.myfalse
              | mybool.mytrue => mybool_eqb b8 c8

def String_eqb : String_string → String_string → mybool
| String_string.EmptyString, String_string.EmptyString => mybool.mytrue
| String_string.String a1 s1, String_string.String a2 s2 =>
  match Ascii_eqb a1 a2 with
  | mybool.myfalse => mybool.myfalse
  | mybool.mytrue => String_eqb s1 s2
| _, _ => mybool.myfalse

-- ================================================================
-- Logic types (will become SProp in Rocq)
-- ================================================================

-- Equality type - universe polymorphic (works for Type, Type 1, etc.)
universe u
inductive Corelib_Init_Logic_eq {A : Sort u} (a : A) : A → Prop
| refl : Corelib_Init_Logic_eq a a

-- Equality for Prop (needed for SProp translation)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} (a : A) : A → Prop
| refl : Corelib_Init_Logic_eq_Prop a a

-- True type as Prop (use Lean's built-in True with alias for export)
def True_alias : Prop := True
def True_I : True_alias := True.intro

-- False type as Prop (use Lean's built-in False with alias)
def False_alias : Prop := False

-- not (Logic.not)
def Logic_not (P : Prop) : Prop := P → False_alias

-- and
inductive PandType (A B : Prop) : Prop
| conj : A → B → PandType A B

-- or
inductive PorType (A B : Prop) : Prop
| or_introl : A → PorType A B
| or_intror : B → PorType A B

-- iff
def iff (A B : Prop) : Prop := PandType (A → B) (B → A)

-- ex
inductive ex {A : Type} (P : A → Prop) : Prop
| intro : ∀ x : A, P x → ex P

-- le (inductive definition for Prop)
inductive le : nat → nat → Prop
| le_n : ∀ n : nat, le n n
| le_S : ∀ n m : nat, le n m → le n (nat.S m)

-- ================================================================
-- Polymorphic list (for Poly chapter)
-- ================================================================

inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type
| nil : Original_LF__DOT__Poly_LF_Poly_list X
| cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

def Original_LF__DOT__Poly_LF_Poly_cons (X : Type) : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons

def Original_LF__DOT__Poly_LF_Poly_app (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X
| Original_LF__DOT__Poly_LF_Poly_list.nil, l2 => l2
| Original_LF__DOT__Poly_LF_Poly_list.cons h t, l2 => Original_LF__DOT__Poly_LF_Poly_list.cons h (Original_LF__DOT__Poly_LF_Poly_app X t l2)

def Original_LF__DOT__Poly_LF_Poly_length (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X → nat
| Original_LF__DOT__Poly_LF_Poly_list.nil => nat.O
| Original_LF__DOT__Poly_LF_Poly_list.cons _ t => nat.S (Original_LF__DOT__Poly_LF_Poly_length X t)

-- Polymorphic option
inductive Original_LF__DOT__Poly_LF_Poly_option (X : Type) : Type
| Some : X → Original_LF__DOT__Poly_LF_Poly_option X
| None : Original_LF__DOT__Poly_LF_Poly_option X

def Original_LF__DOT__Poly_LF_Poly_Some {X : Type} (x : X) : Original_LF__DOT__Poly_LF_Poly_option X := Original_LF__DOT__Poly_LF_Poly_option.Some x
def Original_LF__DOT__Poly_LF_Poly_None (X : Type) : Original_LF__DOT__Poly_LF_Poly_option X := Original_LF__DOT__Poly_LF_Poly_option.None

-- Option/option alias for the standard checker
inductive myoption (A : Type) : Type
| mySome : A → myoption A
| myNone : myoption A

def mySome {A : Type} (x : A) : myoption A := myoption.mySome x
def myNone (A : Type) : myoption A := myoption.myNone

-- ================================================================
-- Prod type
-- ================================================================

inductive myprod (A B : Type) : Type
| mk : A → B → myprod A B

-- ================================================================
-- Standard list (for stdlib list checker)
-- ================================================================

inductive mylist (A : Type) : Type
| mynil : mylist A
| mycons : A → mylist A → mylist A

def mynil (A : Type) : mylist A := mylist.mynil
def mycons {A : Type} (x : A) (l : mylist A) : mylist A := mylist.mycons x l

-- In for mylist (for List.In isomorphism)
inductive mylist_In {A : Type} (x : A) : mylist A → Prop
| here : ∀ l : mylist A, mylist_In x (mylist.mycons x l)
| there : ∀ (y : A) (l : mylist A), mylist_In x l → mylist_In x (mylist.mycons y l)

-- ================================================================
-- Maps (total_map and partial_map)
-- ================================================================

def Original_LF__DOT__Maps_LF_Maps_total__map (A : Type) : Type := String_string → A

def Original_LF__DOT__Maps_LF_Maps_t__empty {A : Type} (v : A) : Original_LF__DOT__Maps_LF_Maps_total__map A :=
  fun _ => v

def Original_LF__DOT__Maps_LF_Maps_t__update {A : Type} (m : Original_LF__DOT__Maps_LF_Maps_total__map A)
    (x : String_string) (v : A) : Original_LF__DOT__Maps_LF_Maps_total__map A :=
  fun x' => match String_eqb x x' with
            | mybool.mytrue => v
            | mybool.myfalse => m x'

def Original_LF__DOT__Maps_LF_Maps_partial__map (A : Type) : Type := Original_LF__DOT__Maps_LF_Maps_total__map (myoption A)

-- ================================================================
-- Imp types
-- ================================================================

-- State type
def Original_LF__DOT__Imp_LF_Imp_state : Type := Original_LF__DOT__Maps_LF_Maps_total__map nat

-- empty_st
def Original_LF__DOT__Imp_LF_Imp_empty__st : Original_LF__DOT__Imp_LF_Imp_state :=
  fun _ => nat.O

-- X, Y, Z variable definitions
-- 'X' = 88 = 01011000, bits: b0=0,b1=0,b2=0,b3=1,b4=1,b5=0,b6=1,b7=0
def Original_LF__DOT__Imp_LF_Imp_X : String_string :=
  String_string.String
    (Ascii_ascii.Ascii mybool.myfalse mybool.myfalse mybool.myfalse mybool.mytrue
                       mybool.mytrue mybool.myfalse mybool.mytrue mybool.myfalse)
    String_string.EmptyString

-- 'Y' = 89 = 01011001, bits: b0=1,b1=0,b2=0,b3=1,b4=1,b5=0,b6=1,b7=0
def Original_LF__DOT__Imp_LF_Imp_Y : String_string :=
  String_string.String
    (Ascii_ascii.Ascii mybool.mytrue mybool.myfalse mybool.myfalse mybool.mytrue
                       mybool.mytrue mybool.myfalse mybool.mytrue mybool.myfalse)
    String_string.EmptyString

-- 'Z' = 90 = 01011010, bits: b0=0,b1=1,b2=0,b3=1,b4=1,b5=0,b6=1,b7=0
def Original_LF__DOT__Imp_LF_Imp_Z : String_string :=
  String_string.String
    (Ascii_ascii.Ascii mybool.myfalse mybool.mytrue mybool.myfalse mybool.mytrue
                       mybool.mytrue mybool.myfalse mybool.mytrue mybool.myfalse)
    String_string.EmptyString

-- aexp
inductive Original_LF__DOT__Imp_LF_Imp_aexp : Type
| ANum : nat → Original_LF__DOT__Imp_LF_Imp_aexp
| AId : String_string → Original_LF__DOT__Imp_LF_Imp_aexp
| APlus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp
| AMinus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp
| AMult : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp

def Original_LF__DOT__Imp_LF_Imp_ANum : nat → Original_LF__DOT__Imp_LF_Imp_aexp := Original_LF__DOT__Imp_LF_Imp_aexp.ANum
def Original_LF__DOT__Imp_LF_Imp_AId : String_string → Original_LF__DOT__Imp_LF_Imp_aexp := Original_LF__DOT__Imp_LF_Imp_aexp.AId
def Original_LF__DOT__Imp_LF_Imp_APlus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp := Original_LF__DOT__Imp_LF_Imp_aexp.APlus
def Original_LF__DOT__Imp_LF_Imp_AMinus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp := Original_LF__DOT__Imp_LF_Imp_aexp.AMinus
def Original_LF__DOT__Imp_LF_Imp_AMult : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp := Original_LF__DOT__Imp_LF_Imp_aexp.AMult

-- bexp
inductive Original_LF__DOT__Imp_LF_Imp_bexp : Type
| BTrue : Original_LF__DOT__Imp_LF_Imp_bexp
| BFalse : Original_LF__DOT__Imp_LF_Imp_bexp
| BEq : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
| BNeq : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
| BLe : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
| BGt : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
| BNot : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp
| BAnd : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp

def Original_LF__DOT__Imp_LF_Imp_BTrue : Original_LF__DOT__Imp_LF_Imp_bexp := Original_LF__DOT__Imp_LF_Imp_bexp.BTrue
def Original_LF__DOT__Imp_LF_Imp_BFalse : Original_LF__DOT__Imp_LF_Imp_bexp := Original_LF__DOT__Imp_LF_Imp_bexp.BFalse
def Original_LF__DOT__Imp_LF_Imp_BEq : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp := Original_LF__DOT__Imp_LF_Imp_bexp.BEq
def Original_LF__DOT__Imp_LF_Imp_BNeq : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp := Original_LF__DOT__Imp_LF_Imp_bexp.BNeq
def Original_LF__DOT__Imp_LF_Imp_BLe : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp := Original_LF__DOT__Imp_LF_Imp_bexp.BLe
def Original_LF__DOT__Imp_LF_Imp_BGt : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp := Original_LF__DOT__Imp_LF_Imp_bexp.BGt
def Original_LF__DOT__Imp_LF_Imp_BNot : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp := Original_LF__DOT__Imp_LF_Imp_bexp.BNot
def Original_LF__DOT__Imp_LF_Imp_BAnd : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp := Original_LF__DOT__Imp_LF_Imp_bexp.BAnd

-- com (commands)
inductive Original_LF__DOT__Imp_LF_Imp_com : Type
| CSkip : Original_LF__DOT__Imp_LF_Imp_com
| CAsgn : String_string → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_com
| CSeq : Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com
| CIf : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com
| CWhile : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com

def Original_LF__DOT__Imp_LF_Imp_CSkip : Original_LF__DOT__Imp_LF_Imp_com := Original_LF__DOT__Imp_LF_Imp_com.CSkip
def Original_LF__DOT__Imp_LF_Imp_CAsgn : String_string → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_com := Original_LF__DOT__Imp_LF_Imp_com.CAsgn
def Original_LF__DOT__Imp_LF_Imp_CSeq : Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com := Original_LF__DOT__Imp_LF_Imp_com.CSeq
def Original_LF__DOT__Imp_LF_Imp_CIf : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com := Original_LF__DOT__Imp_LF_Imp_com.CIf
def Original_LF__DOT__Imp_LF_Imp_CWhile : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com := Original_LF__DOT__Imp_LF_Imp_com.CWhile

-- aeval
def Original_LF__DOT__Imp_LF_Imp_aeval :
    (String_string → nat) →
    Original_LF__DOT__Imp_LF_Imp_aexp →
    nat
| _st, Original_LF__DOT__Imp_LF_Imp_aexp.ANum n => n
| st, Original_LF__DOT__Imp_LF_Imp_aexp.AId x => st x
| st, Original_LF__DOT__Imp_LF_Imp_aexp.APlus a1 a2 =>
    Nat_add (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
| st, Original_LF__DOT__Imp_LF_Imp_aexp.AMinus a1 a2 =>
    Nat_sub (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
| st, Original_LF__DOT__Imp_LF_Imp_aexp.AMult a1 a2 =>
    Nat_mul (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)

-- beval
def Original_LF__DOT__Imp_LF_Imp_beval :
    (String_string → nat) →
    Original_LF__DOT__Imp_LF_Imp_bexp →
    mybool
| _st, Original_LF__DOT__Imp_LF_Imp_bexp.BTrue => mybool.mytrue
| _st, Original_LF__DOT__Imp_LF_Imp_bexp.BFalse => mybool.myfalse
| st, Original_LF__DOT__Imp_LF_Imp_bexp.BEq a1 a2 =>
    nat_eqb (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
| st, Original_LF__DOT__Imp_LF_Imp_bexp.BNeq a1 a2 =>
    negb (nat_eqb (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2))
| st, Original_LF__DOT__Imp_LF_Imp_bexp.BLe a1 a2 =>
    nat_leb (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
| st, Original_LF__DOT__Imp_LF_Imp_bexp.BGt a1 a2 =>
    negb (nat_leb (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2))
| st, Original_LF__DOT__Imp_LF_Imp_bexp.BNot b1 =>
    negb (Original_LF__DOT__Imp_LF_Imp_beval st b1)
| st, Original_LF__DOT__Imp_LF_Imp_bexp.BAnd b1 b2 =>
    andb (Original_LF__DOT__Imp_LF_Imp_beval st b1) (Original_LF__DOT__Imp_LF_Imp_beval st b2)

-- ================================================================
-- Rel types
-- ================================================================

def Original_LF_Rel_relation (X : Type) : Type := X → X → Prop

-- transitive relation property
def Original_LF_Rel_transitive {X : Type} (R : Original_LF_Rel_relation X) : Prop :=
  ∀ a b c : X, R a b → R b c → R a c

-- reflexive relation property
def Original_LF_Rel_reflexive {X : Type} (R : Original_LF_Rel_relation X) : Prop :=
  ∀ a : X, R a a

-- symmetric relation property
def Original_LF_Rel_symmetric {X : Type} (R : Original_LF_Rel_relation X) : Prop :=
  ∀ a b : X, R a b → R b a

-- antisymmetric relation property
def Original_LF_Rel_antisymmetric {X : Type} (R : Original_LF_Rel_relation X) : Prop :=
  ∀ a b : X, R a b → R b a → @Corelib_Init_Logic_eq X a b

-- ================================================================
-- Logic In
-- ================================================================

inductive Original_LF__DOT__Logic_LF_Logic_In {A : Type} (x : A) : Original_LF__DOT__Poly_LF_Poly_list A → Prop
| here : ∀ l : Original_LF__DOT__Poly_LF_Poly_list A, Original_LF__DOT__Logic_LF_Logic_In x (Original_LF__DOT__Poly_LF_Poly_list.cons x l)
| there : ∀ y l, Original_LF__DOT__Logic_LF_Logic_In x l → Original_LF__DOT__Logic_LF_Logic_In x (Original_LF__DOT__Poly_LF_Poly_list.cons y l)

-- ================================================================
-- RGB and Color types
-- ================================================================

inductive Original_LF__DOT__Basics_LF_Basics_rgb : Type
| red : Original_LF__DOT__Basics_LF_Basics_rgb
| green : Original_LF__DOT__Basics_LF_Basics_rgb
| blue : Original_LF__DOT__Basics_LF_Basics_rgb

inductive Original_LF__DOT__Basics_LF_Basics_color : Type
| black : Original_LF__DOT__Basics_LF_Basics_color
| white : Original_LF__DOT__Basics_LF_Basics_color
| primary : Original_LF__DOT__Basics_LF_Basics_rgb → Original_LF__DOT__Basics_LF_Basics_color

def Original_LF__DOT__Basics_LF_Basics_monochrome (c : Original_LF__DOT__Basics_LF_Basics_color) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match c with
  | Original_LF__DOT__Basics_LF_Basics_color.black => Original_LF__DOT__Basics_LF_Basics_bool.true
  | Original_LF__DOT__Basics_LF_Basics_color.white => Original_LF__DOT__Basics_LF_Basics_bool.true
  | Original_LF__DOT__Basics_LF_Basics_color.primary _ => Original_LF__DOT__Basics_LF_Basics_bool.false

-- ================================================================
-- Poly: doit3times, filter, countoddmembers'
-- ================================================================

def Original_LF__DOT__Poly_LF_Poly_doit3times (X : Type) (f : X → X) (n : X) : X :=
  f (f (f n))

def Original_LF__DOT__Poly_LF_Poly_filter (X : Type) (test : X → Original_LF__DOT__Basics_LF_Basics_bool) : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X
| Original_LF__DOT__Poly_LF_Poly_list.nil => Original_LF__DOT__Poly_LF_Poly_list.nil
| Original_LF__DOT__Poly_LF_Poly_list.cons h t =>
    match test h with
    | Original_LF__DOT__Basics_LF_Basics_bool.true => Original_LF__DOT__Poly_LF_Poly_list.cons h (Original_LF__DOT__Poly_LF_Poly_filter X test t)
    | Original_LF__DOT__Basics_LF_Basics_bool.false => Original_LF__DOT__Poly_LF_Poly_filter X test t

def Original_LF__DOT__Poly_LF_Poly_countoddmembers' (l : Original_LF__DOT__Poly_LF_Poly_list nat) : nat :=
  Original_LF__DOT__Poly_LF_Poly_length nat (Original_LF__DOT__Poly_LF_Poly_filter nat Original_LF__DOT__Basics_LF_Basics_odd l)

-- ================================================================
-- Tactics: sillyfun
-- ================================================================

def Original_LF__DOT__Tactics_LF_Tactics_sillyfun (n : nat) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match Original_LF__DOT__Basics_LF_Basics_eqb n (nat.S (nat.S (nat.S nat.O))) with
  | Original_LF__DOT__Basics_LF_Basics_bool.true => Original_LF__DOT__Basics_LF_Basics_bool.false
  | Original_LF__DOT__Basics_LF_Basics_bool.false =>
    match Original_LF__DOT__Basics_LF_Basics_eqb n (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))) with
    | Original_LF__DOT__Basics_LF_Basics_bool.true => Original_LF__DOT__Basics_LF_Basics_bool.false
    | Original_LF__DOT__Basics_LF_Basics_bool.false => Original_LF__DOT__Basics_LF_Basics_bool.false

-- ================================================================
-- Church numerals (cnat)
-- ================================================================

def Original_LF__DOT__Poly_LF_Poly_Exercises_cnat : Type 1 :=
  (X : Type) → (X → X) → X → X

-- Equality for Type 1 (for cnat) - defined early so it can be used in axioms
inductive Corelib_Init_Logic_eq_Type1 {A : Type 1} (a : A) : A → Prop
| refl : Corelib_Init_Logic_eq_Type1 a a

def Original_LF__DOT__Poly_LF_Poly_Exercises_zero : Original_LF__DOT__Poly_LF_Poly_Exercises_cnat :=
  fun (X : Type) (_f : X → X) (x : X) => x

def Original_LF__DOT__Poly_LF_Poly_Exercises_one : Original_LF__DOT__Poly_LF_Poly_Exercises_cnat :=
  fun (X : Type) (f : X → X) (x : X) => f x

def Original_LF__DOT__Poly_LF_Poly_Exercises_two : Original_LF__DOT__Poly_LF_Poly_Exercises_cnat :=
  fun (X : Type) (f : X → X) (x : X) => f (f x)

def Original_LF__DOT__Poly_LF_Poly_Exercises_three : Original_LF__DOT__Poly_LF_Poly_Exercises_cnat :=
  fun (X : Type) (f : X → X) (x : X) => f (f (f x))

-- scc (successor for church numerals) - proper definition
def Original_LF__DOT__Poly_LF_Poly_Exercises_scc 
  (n : Original_LF__DOT__Poly_LF_Poly_Exercises_cnat) : Original_LF__DOT__Poly_LF_Poly_Exercises_cnat :=
  fun (X : Type) (f : X → X) (x : X) => f (n X f x)

-- scc_1 : scc zero = one - proved by reflexivity
theorem Original_LF__DOT__Poly_LF_Poly_Exercises_scc__1 :
  @Corelib_Init_Logic_eq_Type1 Original_LF__DOT__Poly_LF_Poly_Exercises_cnat
    (Original_LF__DOT__Poly_LF_Poly_Exercises_scc Original_LF__DOT__Poly_LF_Poly_Exercises_zero)
    Original_LF__DOT__Poly_LF_Poly_Exercises_one := Corelib_Init_Logic_eq_Type1.refl

-- plus for church numerals
def Original_LF__DOT__Poly_LF_Poly_Exercises_plus 
  (n m : Original_LF__DOT__Poly_LF_Poly_Exercises_cnat) : Original_LF__DOT__Poly_LF_Poly_Exercises_cnat :=
  fun (X : Type) (f : X → X) (x : X) => n X f (m X f x)

-- mult for church numerals
def Original_LF__DOT__Poly_LF_Poly_Exercises_mult 
  (n m : Original_LF__DOT__Poly_LF_Poly_Exercises_cnat) : Original_LF__DOT__Poly_LF_Poly_Exercises_cnat :=
  fun (X : Type) (f : X → X) => n X (m X f)

-- exp (exponentiation for church numerals) - proper definition
-- exp n m = n^m, using Church encoding: fun X => m (X -> X) (n X)
def Original_LF__DOT__Poly_LF_Poly_Exercises_exp 
  (n m : Original_LF__DOT__Poly_LF_Poly_Exercises_cnat) : Original_LF__DOT__Poly_LF_Poly_Exercises_cnat :=
  fun (X : Type) => m (X → X) (n X)

-- exp_2 : exp three zero = one - proved by reflexivity
theorem Original_LF__DOT__Poly_LF_Poly_Exercises_exp__2 :
  @Corelib_Init_Logic_eq_Type1 Original_LF__DOT__Poly_LF_Poly_Exercises_cnat
    (Original_LF__DOT__Poly_LF_Poly_Exercises_exp 
      Original_LF__DOT__Poly_LF_Poly_Exercises_three 
      Original_LF__DOT__Poly_LF_Poly_Exercises_zero)
    Original_LF__DOT__Poly_LF_Poly_Exercises_one := Corelib_Init_Logic_eq_Type1.refl

-- one_church_peano : one nat S O = 1 - proved by reflexivity
theorem Original_LF__DOT__Poly_LF_Poly_Exercises_one__church__peano :
  @Corelib_Init_Logic_eq nat
    (Original_LF__DOT__Poly_LF_Poly_Exercises_one nat nat.S nat.O)
    (nat.S nat.O) := Corelib_Init_Logic_eq.refl

-- mult_2: mult zero (plus three three) = zero - proved by reflexivity
theorem Original_LF__DOT__Poly_LF_Poly_Exercises_mult__2 :
  @Corelib_Init_Logic_eq_Type1 Original_LF__DOT__Poly_LF_Poly_Exercises_cnat
    (Original_LF__DOT__Poly_LF_Poly_Exercises_mult
      Original_LF__DOT__Poly_LF_Poly_Exercises_zero
      (Original_LF__DOT__Poly_LF_Poly_Exercises_plus
        Original_LF__DOT__Poly_LF_Poly_Exercises_three
        Original_LF__DOT__Poly_LF_Poly_Exercises_three))
    Original_LF__DOT__Poly_LF_Poly_Exercises_zero := Corelib_Init_Logic_eq_Type1.refl

-- ================================================================
-- fold and fold_length
-- ================================================================

def Original_LF__DOT__Poly_LF_Poly_fold {X Y : Type} (f : X → Y → Y) : Original_LF__DOT__Poly_LF_Poly_list X → Y → Y
| Original_LF__DOT__Poly_LF_Poly_list.nil, b => b
| Original_LF__DOT__Poly_LF_Poly_list.cons h t, b => f h (Original_LF__DOT__Poly_LF_Poly_fold f t b)

def Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length {X : Type} (l : Original_LF__DOT__Poly_LF_Poly_list X) : nat :=
  Original_LF__DOT__Poly_LF_Poly_fold (fun _ n => nat.S n) l nat.O

-- test_fold_length1 : fold_length [4;7;0] = 3 (Admitted)
axiom Original_LF__DOT__Poly_LF_Poly_Exercises_test__fold__length1 :
  @Corelib_Init_Logic_eq nat
    (Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length 
      (Original_LF__DOT__Poly_LF_Poly_list.cons (nat.S (nat.S (nat.S (nat.S nat.O))))
        (Original_LF__DOT__Poly_LF_Poly_list.cons (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))))
          (Original_LF__DOT__Poly_LF_Poly_list.cons nat.O
            Original_LF__DOT__Poly_LF_Poly_list.nil))))
    (nat.S (nat.S (nat.S nat.O)))

-- fold_length_correct : forall X (l : list X), fold_length l = length l (Admitted)
axiom Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length__correct :
  ∀ (X : Type) (l : Original_LF__DOT__Poly_LF_Poly_list X),
    @Corelib_Init_Logic_eq nat
      (Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length l)
      (Original_LF__DOT__Poly_LF_Poly_length X l)

-- ================================================================
-- ev (EvPlayground.ev) - evenness predicate
-- ================================================================

inductive Original_LF__DOT__IndProp_LF_IndProp_ev__playground_ev : nat → Prop
| ev_0 : Original_LF__DOT__IndProp_LF_IndProp_ev__playground_ev nat.O
| ev_SS : ∀ (n : nat), Original_LF__DOT__IndProp_LF_IndProp_ev__playground_ev n → 
                        Original_LF__DOT__IndProp_LF_IndProp_ev__playground_ev (nat.S (nat.S n))

-- evSS_ev' : forall n, ev (S (S n)) -> ev n (Admitted)
axiom Original_LF__DOT__IndProp_LF_IndProp_evSS__ev' :
  ∀ (n : nat), Original_LF__DOT__IndProp_LF_IndProp_ev__playground_ev (nat.S (nat.S n)) → 
               Original_LF__DOT__IndProp_LF_IndProp_ev__playground_ev n

-- ================================================================
-- repeat''
-- ================================================================

def Original_LF__DOT__Poly_LF_Poly_repeatSQUOTESQUOTE {X : Type} (x : X) (count : nat) : Original_LF__DOT__Poly_LF_Poly_list X :=
  match count with
  | nat.O => Original_LF__DOT__Poly_LF_Poly_list.nil
  | nat.S count' => Original_LF__DOT__Poly_LF_Poly_list.cons x (Original_LF__DOT__Poly_LF_Poly_repeatSQUOTESQUOTE x count')

-- ================================================================
-- Tactics: injection_ex1 and injection_ex3
-- ================================================================

-- injection_ex1 : forall (n m o : nat), [n;m] = [o;o] -> n = m (Admitted)
axiom Original_LF__DOT__Tactics_LF_Tactics_injection__ex1 :
  ∀ (n m o : nat),
    @Corelib_Init_Logic_eq (Original_LF__DOT__Poly_LF_Poly_list nat)
      (Original_LF__DOT__Poly_LF_Poly_list.cons n 
        (Original_LF__DOT__Poly_LF_Poly_list.cons m Original_LF__DOT__Poly_LF_Poly_list.nil))
      (Original_LF__DOT__Poly_LF_Poly_list.cons o 
        (Original_LF__DOT__Poly_LF_Poly_list.cons o Original_LF__DOT__Poly_LF_Poly_list.nil)) →
    @Corelib_Init_Logic_eq nat n m

-- injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
--   x :: y :: l = z :: j -> j = z :: l -> x = y (Admitted)
axiom Original_LF__DOT__Tactics_LF_Tactics_injection__ex3 :
  ∀ (X : Type) (x y z : X) (l j : Original_LF__DOT__Poly_LF_Poly_list X),
    @Corelib_Init_Logic_eq (Original_LF__DOT__Poly_LF_Poly_list X)
      (Original_LF__DOT__Poly_LF_Poly_list.cons x 
        (Original_LF__DOT__Poly_LF_Poly_list.cons y l))
      (Original_LF__DOT__Poly_LF_Poly_list.cons z j) →
    @Corelib_Init_Logic_eq (Original_LF__DOT__Poly_LF_Poly_list X) j 
      (Original_LF__DOT__Poly_LF_Poly_list.cons z l) →
    @Corelib_Init_Logic_eq X x y

-- ================================================================
-- Imp: silly1
-- ================================================================

-- silly1 : forall P : Prop, P -> P (Admitted in Original Imp.AExp)
axiom Original_LF__DOT__Imp_LF_Imp_AExp_silly1 :
  ∀ (P : Prop), P → P

-- ================================================================
-- Admitted theorems from Original.v 
-- ================================================================

-- andb_commutative'' is Admitted
axiom Original_LF__DOT__Basics_LF_Basics_andb__commutative'' :
  ∀ (b c : Original_LF__DOT__Basics_LF_Basics_bool),
  Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_andb b c)
                        (Original_LF__DOT__Basics_LF_Basics_andb c b)

-- test_orb4: orb true true = true
def Original_LF__DOT__Basics_LF_Basics_test__orb4 :
  Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_orb Original_LF__DOT__Basics_LF_Basics_bool.true Original_LF__DOT__Basics_LF_Basics_bool.true)
                        Original_LF__DOT__Basics_LF_Basics_bool.true :=
  Corelib_Init_Logic_eq.refl

-- example_bexp: true && ~(X <= 4)
def Original_LF__DOT__Imp_LF_Imp_example__bexp : Original_LF__DOT__Imp_LF_Imp_bexp :=
  Original_LF__DOT__Imp_LF_Imp_bexp.BAnd Original_LF__DOT__Imp_LF_Imp_bexp.BTrue 
    (Original_LF__DOT__Imp_LF_Imp_bexp.BNot (Original_LF__DOT__Imp_LF_Imp_bexp.BLe 
      (Original_LF__DOT__Imp_LF_Imp_aexp.AId Original_LF__DOT__Imp_LF_Imp_X) 
      (Original_LF__DOT__Imp_LF_Imp_aexp.ANum (nat.S (nat.S (nat.S (nat.S nat.O)))))))

-- list123''' = [1;2;3]
def Original_LF__DOT__Poly_LF_Poly_list123''' : Original_LF__DOT__Poly_LF_Poly_list nat :=
  Original_LF__DOT__Poly_LF_Poly_list.cons (nat.S nat.O) 
    (Original_LF__DOT__Poly_LF_Poly_list.cons (nat.S (nat.S nat.O)) 
      (Original_LF__DOT__Poly_LF_Poly_list.cons (nat.S (nat.S (nat.S nat.O))) 
        Original_LF__DOT__Poly_LF_Poly_list.nil))

-- test_countoddmembers'2: countoddmembers' [0;2;4] = 0
axiom Original_LF__DOT__Poly_LF_Poly_test__countoddmembers'2 :
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__Poly_LF_Poly_countoddmembers' 
      (Original_LF__DOT__Poly_LF_Poly_list.cons nat.O 
        (Original_LF__DOT__Poly_LF_Poly_list.cons (nat.S (nat.S nat.O)) 
          (Original_LF__DOT__Poly_LF_Poly_list.cons (nat.S (nat.S (nat.S (nat.S nat.O)))) 
            Original_LF__DOT__Poly_LF_Poly_list.nil))))
    nat.O

-- sillyfun_false: forall n, sillyfun n = false
axiom Original_LF__DOT__Tactics_LF_Tactics_sillyfun__false :
  ∀ (n : nat), Corelib_Init_Logic_eq (Original_LF__DOT__Tactics_LF_Tactics_sillyfun n) Original_LF__DOT__Basics_LF_Basics_bool.false

-- even_42_bool: even 42 = true
axiom Original_LF__DOT__Logic_LF_Logic_even__42__bool :
  Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_even 
    (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))))))))))))))))))))))))))))))))))))))))) 
    Original_LF__DOT__Basics_LF_Basics_bool.true

-- apply_iff_example1
axiom Original_LF__DOT__Logic_LF_Logic_apply__iff__example1 :
  ∀ (P Q R : Prop), iff P Q → (Q → R) → (P → R)

-- le_trans
axiom Original_LF__DOT__IndProp_LF_IndProp_le__trans :
  ∀ (m n o : nat), le m n → le n o → le m o

-- le1: another le relation (like le but named le1)
inductive Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le1 : nat → nat → Prop
| le1_n : ∀ n, Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le1 n n
| le1_S : ∀ n m, Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le1 n m → 
                  Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le1 n (nat.S m)
