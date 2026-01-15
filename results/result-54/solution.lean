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

def myZero : nat := nat.O
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

-- Predecessor
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

-- Option type
inductive option (A : Type) : Type where
  | None : option A
  | Some : A → option A

def None {A : Type} : option A := option.None
def Some {A : Type} (x : A) : option A := option.Some x

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

-- Original.False (different from Prop False)
inductive Original_False : Prop where

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

-- or (disjunction)
inductive or (A B : Prop) : Prop where
  | inl : A → or A B
  | inr : B → or A B

-- List membership
def List_In {A : Type} (x : A) : list A → Prop
  | list.nil => MyFalse
  | list.cons x' l' => or (Corelib_Init_Logic_eq x' x) (List_In x l')

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

-- andb on LF.Basics.bool
def Original_LF__DOT__Basics_LF_Basics_andb : Original_LF__DOT__Basics_LF_Basics_bool → Original_LF__DOT__Basics_LF_Basics_bool → Original_LF__DOT__Basics_LF_Basics_bool
  | Original_LF__DOT__Basics_LF_Basics_bool.true, b2 => b2
  | Original_LF__DOT__Basics_LF_Basics_bool.false, _ => Original_LF__DOT__Basics_LF_Basics_bool.false

-- eqb on nat in LF.Basics
def Original_LF__DOT__Basics_LF_Basics_eqb : nat → nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.true
  | nat.S n, nat.S m => Original_LF__DOT__Basics_LF_Basics_eqb n m
  | _, _ => Original_LF__DOT__Basics_LF_Basics_bool.false

-- nandb: not (andb b1 b2)
def Original_LF__DOT__Basics_LF_Basics_nandb : Original_LF__DOT__Basics_LF_Basics_bool → Original_LF__DOT__Basics_LF_Basics_bool → Original_LF__DOT__Basics_LF_Basics_bool
  | Original_LF__DOT__Basics_LF_Basics_bool.true, Original_LF__DOT__Basics_LF_Basics_bool.true => Original_LF__DOT__Basics_LF_Basics_bool.false
  | _, _ => Original_LF__DOT__Basics_LF_Basics_bool.true

-- test_nandb4: nandb true true = false
def Original_LF__DOT__Basics_LF_Basics_test__nandb4 : Corelib_Init_Logic_eq 
  (Original_LF__DOT__Basics_LF_Basics_nandb Original_LF__DOT__Basics_LF_Basics_true Original_LF__DOT__Basics_LF_Basics_true)
  Original_LF__DOT__Basics_LF_Basics_false := Corelib_Init_Logic_eq.refl _

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

-- filter function
def Original_LF__DOT__Poly_LF_Poly_filter {X : Type} (test : X → Original_LF__DOT__Basics_LF_Basics_bool) : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X
  | Original_LF__DOT__Poly_LF_Poly_list.nil => Original_LF__DOT__Poly_LF_Poly_list.nil
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t =>
    match test h with
    | Original_LF__DOT__Basics_LF_Basics_bool.true => Original_LF__DOT__Poly_LF_Poly_list.cons h (Original_LF__DOT__Poly_LF_Poly_filter test t)
    | Original_LF__DOT__Basics_LF_Basics_bool.false => Original_LF__DOT__Poly_LF_Poly_filter test t

-- ============================================================
-- Original.LF_DOT_Logic definitions (In - needed early for IndProp)
-- ============================================================

-- not definition (for Original.LF.Logic)
def Original_LF__DOT__Logic_LF_Logic_not (P : Prop) : Prop := P → Original_False

-- In (membership in list)
def Original_LF__DOT__Logic_LF_Logic_In {X : Type} (x : X) : Original_LF__DOT__Poly_LF_Poly_list X → Prop
  | Original_LF__DOT__Poly_LF_Poly_list.nil => MyFalse
  | Original_LF__DOT__Poly_LF_Poly_list.cons x' l' => or (Corelib_Init_Logic_eq x' x) (Original_LF__DOT__Logic_LF_Logic_In x l')

-- in_not_nil_42_take2: In 42 l -> l <> nil
def Original_LF__DOT__Logic_LF_Logic_in__not__nil__42__take2 (l : Original_LF__DOT__Poly_LF_Poly_list nat)
  (H : Original_LF__DOT__Logic_LF_Logic_In (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))))))))))))))))))))))))))))))))))))))) l)
  (Heq : Corelib_Init_Logic_eq l (Original_LF__DOT__Poly_LF_Poly_list.nil)) : MyFalse :=
  match l, H, Heq with
  | Original_LF__DOT__Poly_LF_Poly_list.nil, H', Corelib_Init_Logic_eq.refl _ => H'

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
-- Original.LF_DOT_Poly additional definitions (fold, flat_map)
-- ============================================================

-- fold function
def Original_LF__DOT__Poly_LF_Poly_fold {X Y : Type} (f : X → Y → Y) : Original_LF__DOT__Poly_LF_Poly_list X → Y → Y
  | Original_LF__DOT__Poly_LF_Poly_list.nil, b => b
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t, b => f h (Original_LF__DOT__Poly_LF_Poly_fold f t b)

-- flat_map (Admitted in original, so axiom)
axiom Original_LF__DOT__Poly_LF_Poly_flat__map : ∀ {X Y : Type}, (X → Original_LF__DOT__Poly_LF_Poly_list Y) → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list Y

-- fold_example1 (Admitted)
axiom Original_LF__DOT__Poly_LF_Poly_fold__example1 : Corelib_Init_Logic_eq
  (Original_LF__DOT__Poly_LF_Poly_fold Original_LF__DOT__Basics_LF_Basics_andb
    (Original_LF__DOT__Poly_LF_Poly_cons Original_LF__DOT__Basics_LF_Basics_bool Original_LF__DOT__Basics_LF_Basics_true
      (Original_LF__DOT__Poly_LF_Poly_cons Original_LF__DOT__Basics_LF_Basics_bool Original_LF__DOT__Basics_LF_Basics_true
        (Original_LF__DOT__Poly_LF_Poly_cons Original_LF__DOT__Basics_LF_Basics_bool Original_LF__DOT__Basics_LF_Basics_false
          (Original_LF__DOT__Poly_LF_Poly_cons Original_LF__DOT__Basics_LF_Basics_bool Original_LF__DOT__Basics_LF_Basics_true
            (Original_LF__DOT__Poly_LF_Poly_nil Original_LF__DOT__Basics_LF_Basics_bool)))))
    Original_LF__DOT__Basics_LF_Basics_true)
  Original_LF__DOT__Basics_LF_Basics_false

-- test_flat_map1 (Admitted)
axiom Original_LF__DOT__Poly_LF_Poly_test__flat__map1 : Corelib_Init_Logic_eq
  (Original_LF__DOT__Poly_LF_Poly_flat__map (fun n => Original_LF__DOT__Poly_LF_Poly_cons nat n (Original_LF__DOT__Poly_LF_Poly_cons nat n (Original_LF__DOT__Poly_LF_Poly_cons nat n (Original_LF__DOT__Poly_LF_Poly_nil nat))))
    (Original_LF__DOT__Poly_LF_Poly_cons nat (nat.S nat.O)
      (Original_LF__DOT__Poly_LF_Poly_cons nat (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))
        (Original_LF__DOT__Poly_LF_Poly_cons nat (nat.S (nat.S (nat.S (nat.S nat.O))))
          (Original_LF__DOT__Poly_LF_Poly_nil nat)))))
  (Original_LF__DOT__Poly_LF_Poly_cons nat (nat.S nat.O)
    (Original_LF__DOT__Poly_LF_Poly_cons nat (nat.S nat.O)
      (Original_LF__DOT__Poly_LF_Poly_cons nat (nat.S nat.O)
        (Original_LF__DOT__Poly_LF_Poly_cons nat (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))
          (Original_LF__DOT__Poly_LF_Poly_cons nat (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))
            (Original_LF__DOT__Poly_LF_Poly_cons nat (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))
              (Original_LF__DOT__Poly_LF_Poly_cons nat (nat.S (nat.S (nat.S (nat.S nat.O))))
                (Original_LF__DOT__Poly_LF_Poly_cons nat (nat.S (nat.S (nat.S (nat.S nat.O))))
                  (Original_LF__DOT__Poly_LF_Poly_cons nat (nat.S (nat.S (nat.S (nat.S nat.O))))
                    (Original_LF__DOT__Poly_LF_Poly_nil nat))))))))))

-- ============================================================
-- Original.LF_DOT_IndProp additional definitions (nostutter)
-- ============================================================

-- nostutter (empty inductive - no constructors in original)
inductive Original_LF__DOT__IndProp_LF_IndProp_nostutter {X : Type} : Original_LF__DOT__Poly_LF_Poly_list X → Prop where

-- test_nostutter_4: nostutter [3;1;1;4] -> False (admitted in original since nostutter is empty)
def Original_LF__DOT__IndProp_LF_IndProp_test__nostutter__4 (H : Original_LF__DOT__IndProp_LF_IndProp_nostutter
  (Original_LF__DOT__Poly_LF_Poly_cons nat (nat.S (nat.S (nat.S nat.O)))
    (Original_LF__DOT__Poly_LF_Poly_cons nat (nat.S nat.O)
      (Original_LF__DOT__Poly_LF_Poly_cons nat (nat.S nat.O)
        (Original_LF__DOT__Poly_LF_Poly_cons nat (nat.S (nat.S (nat.S (nat.S nat.O))))
          (Original_LF__DOT__Poly_LF_Poly_nil nat)))))) : Original_False :=
  nomatch H

-- count function
def Original_LF__DOT__IndProp_LF_IndProp_count (v : nat) : Original_LF__DOT__Poly_LF_Poly_list nat → nat
  | Original_LF__DOT__Poly_LF_Poly_list.nil => nat.O
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t =>
    match Original_LF__DOT__Basics_LF_Basics_eqb v h with
    | Original_LF__DOT__Basics_LF_Basics_bool.true => nat.S (Original_LF__DOT__IndProp_LF_IndProp_count v t)
    | Original_LF__DOT__Basics_LF_Basics_bool.false => Original_LF__DOT__IndProp_LF_IndProp_count v t

-- Reduction lemmas for count
theorem Original_LF__DOT__IndProp_LF_IndProp_count_nil (v : nat) :
  Corelib_Init_Logic_eq (Original_LF__DOT__IndProp_LF_IndProp_count v Original_LF__DOT__Poly_LF_Poly_list.nil) nat.O :=
  Corelib_Init_Logic_eq.refl _

theorem Original_LF__DOT__IndProp_LF_IndProp_count_cons (v h : nat) (t : Original_LF__DOT__Poly_LF_Poly_list nat) :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__IndProp_LF_IndProp_count v (Original_LF__DOT__Poly_LF_Poly_list.cons h t))
    (match Original_LF__DOT__Basics_LF_Basics_eqb v h with
     | Original_LF__DOT__Basics_LF_Basics_bool.true => nat.S (Original_LF__DOT__IndProp_LF_IndProp_count v t)
     | Original_LF__DOT__Basics_LF_Basics_bool.false => Original_LF__DOT__IndProp_LF_IndProp_count v t) :=
  Corelib_Init_Logic_eq.refl _

-- eqbP_practice: count n l = 0 -> In n l -> False (admitted)
-- NOTE: Uses Original_LF__DOT__Logic_LF_Logic_In defined in Logic section below
axiom Original_LF__DOT__IndProp_LF_IndProp_eqbP__practice : ∀ (n : nat) (l : Original_LF__DOT__Poly_LF_Poly_list nat),
  Corelib_Init_Logic_eq (Original_LF__DOT__IndProp_LF_IndProp_count n l) nat.O →
  @Original_LF__DOT__Logic_LF_Logic_In nat n l → MyFalse

-- filter_not_empty_In: (filter (eqb n) l <> nil) -> In n l (admitted)
axiom Original_LF__DOT__IndProp_LF_IndProp_filter__not__empty__In : ∀ (n : nat) (l : Original_LF__DOT__Poly_LF_Poly_list nat),
  (Corelib_Init_Logic_eq (Original_LF__DOT__Poly_LF_Poly_filter (fun x => Original_LF__DOT__Basics_LF_Basics_eqb n x) l) (Original_LF__DOT__Poly_LF_Poly_list.nil) → MyFalse) →
  @Original_LF__DOT__Logic_LF_Logic_In nat n l

-- ============================================================
-- Original.LF_DOT_Tactics definitions (existsb)
-- ============================================================

-- existsb (Admitted in original)
axiom Original_LF__DOT__Tactics_LF_Tactics_existsb : ∀ {X : Type}, (X → Original_LF__DOT__Basics_LF_Basics_bool) → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Basics_LF_Basics_bool

-- test_existsb_1 (Admitted)
axiom Original_LF__DOT__Tactics_LF_Tactics_test__existsb__1 : Corelib_Init_Logic_eq
  (Original_LF__DOT__Tactics_LF_Tactics_existsb (Original_LF__DOT__Basics_LF_Basics_eqb (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))))
    (Original_LF__DOT__Poly_LF_Poly_cons nat nat.O
      (Original_LF__DOT__Poly_LF_Poly_cons nat (nat.S (nat.S nat.O))
        (Original_LF__DOT__Poly_LF_Poly_cons nat (nat.S (nat.S (nat.S nat.O)))
          (Original_LF__DOT__Poly_LF_Poly_cons nat (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))))
            (Original_LF__DOT__Poly_LF_Poly_nil nat))))))
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- trans_eq_example''' (Admitted)
axiom Original_LF__DOT__Tactics_LF_Tactics_trans__eq__example''' : ∀ (a b c d e f : nat),
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__Poly_LF_Poly_cons nat a (Original_LF__DOT__Poly_LF_Poly_cons nat b (Original_LF__DOT__Poly_LF_Poly_nil nat)))
    (Original_LF__DOT__Poly_LF_Poly_cons nat c (Original_LF__DOT__Poly_LF_Poly_cons nat d (Original_LF__DOT__Poly_LF_Poly_nil nat))) →
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__Poly_LF_Poly_cons nat c (Original_LF__DOT__Poly_LF_Poly_cons nat d (Original_LF__DOT__Poly_LF_Poly_nil nat)))
    (Original_LF__DOT__Poly_LF_Poly_cons nat e (Original_LF__DOT__Poly_LF_Poly_cons nat f (Original_LF__DOT__Poly_LF_Poly_nil nat))) →
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__Poly_LF_Poly_cons nat a (Original_LF__DOT__Poly_LF_Poly_cons nat b (Original_LF__DOT__Poly_LF_Poly_nil nat)))
    (Original_LF__DOT__Poly_LF_Poly_cons nat e (Original_LF__DOT__Poly_LF_Poly_cons nat f (Original_LF__DOT__Poly_LF_Poly_nil nat)))

-- ============================================================
-- Original.LF_DOT_Maps additional definitions
-- ============================================================

-- empty map
def Original_LF__DOT__Maps_LF_Maps_empty (A : Type) : Original_LF__DOT__Maps_LF_Maps_total__map (option A) :=
  Original_LF__DOT__Maps_LF_Maps_t__empty (option A) option.None

-- partial_map
def Original_LF__DOT__Maps_LF_Maps_partial__map (A : Type) : Type := Original_LF__DOT__Maps_LF_Maps_total__map (option A)

-- apply_empty lemma (Admitted in Original.v)
axiom Original_LF__DOT__Maps_LF_Maps_apply__empty : ∀ (A : Type) (x : String_string), Corelib_Init_Logic_eq ((Original_LF__DOT__Maps_LF_Maps_empty A) x) option.None

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
-- Original.LF.Rel definitions
-- ============================================================

def Original_LF_Rel_relation (X : Type) : Type := X → X → Prop

def Original_LF_Rel_partial__function {X : Type} (R : Original_LF_Rel_relation X) : Prop :=
  ∀ x y1 y2 : X, R x y1 → R x y2 → Corelib_Init_Logic_eq y1 y2

inductive Original_LF_Rel_total__relation : nat → nat → Prop where
  | total : ∀ n m : nat, Original_LF_Rel_total__relation n m

-- ============================================================
-- Original.LF_DOT_Basics admitted theorems
-- ============================================================

-- andb_commutative' : forall b c, andb b c = andb c b.
axiom Original_LF__DOT__Basics_LF_Basics_andb__commutative' : ∀ b c : Original_LF__DOT__Basics_LF_Basics_bool, Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_andb b c) (Original_LF__DOT__Basics_LF_Basics_andb c b)

-- zero_nbeq_plus_1 : forall n : nat, 0 =? (n + 1) = false.
axiom Original_LF__DOT__Basics_LF_Basics_zero__nbeq__plus__1 : ∀ n : nat, Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_eqb nat.O (Nat_add n (nat.S nat.O))) Original_LF__DOT__Basics_LF_Basics_bool.false

-- ============================================================
-- Original.LF_DOT_Logic additional definitions  
-- ============================================================

-- double_neg : forall P : Prop, P -> ~~P
-- This is Admitted in the original, so we make it an axiom
axiom Original_LF__DOT__Logic_LF_Logic_double__neg : ∀ P : Prop, P → Logic_not (Logic_not P)

-- ============================================================
-- Original.LF_DOT_Lists definitions
-- ============================================================

-- natlist type
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natlist : Type where
  | nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist

def Original_LF__DOT__Lists_LF_Lists_NatList_nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil

def Original_LF__DOT__Lists_LF_Lists_NatList_cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons

-- bag is alias for natlist
def Original_LF__DOT__Lists_LF_Lists_NatList_bag : Type := Original_LF__DOT__Lists_LF_Lists_NatList_natlist

-- included function (Admitted in original)
axiom Original_LF__DOT__Lists_LF_Lists_NatList_included : Original_LF__DOT__Lists_LF_Lists_NatList_bag → Original_LF__DOT__Lists_LF_Lists_NatList_bag → Original_LF__DOT__Basics_LF_Basics_bool

-- test_included1 (Admitted)
axiom Original_LF__DOT__Lists_LF_Lists_NatList_test__included1 : Corelib_Init_Logic_eq (Original_LF__DOT__Lists_LF_Lists_NatList_included (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S nat.O) (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S (nat.S nat.O)) Original_LF__DOT__Lists_LF_Lists_NatList_nil)) (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S (nat.S nat.O)) (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S nat.O) (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S (nat.S (nat.S (nat.S nat.O)))) (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S nat.O) Original_LF__DOT__Lists_LF_Lists_NatList_nil))))) Original_LF__DOT__Basics_LF_Basics_bool.true

-- ============================================================
-- Original.LF_DOT_Imp.AExp definitions (without state)
-- ============================================================

inductive Original_LF__DOT__Imp_LF_Imp_AExp_aexp : Type where
  | ANum : nat → Original_LF__DOT__Imp_LF_Imp_AExp_aexp
  | APlus : Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp
  | AMinus : Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp
  | AMult : Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp

def Original_LF__DOT__Imp_LF_Imp_AExp_ANum : nat → Original_LF__DOT__Imp_LF_Imp_AExp_aexp := Original_LF__DOT__Imp_LF_Imp_AExp_aexp.ANum
def Original_LF__DOT__Imp_LF_Imp_AExp_APlus : Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp := Original_LF__DOT__Imp_LF_Imp_AExp_aexp.APlus

def Original_LF__DOT__Imp_LF_Imp_AExp_aeval : Original_LF__DOT__Imp_LF_Imp_AExp_aexp → nat
  | Original_LF__DOT__Imp_LF_Imp_AExp_aexp.ANum n => n
  | Original_LF__DOT__Imp_LF_Imp_AExp_aexp.APlus a1 a2 => Nat_add (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a1) (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a2)
  | Original_LF__DOT__Imp_LF_Imp_AExp_aexp.AMinus a1 a2 => Nat_sub (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a1) (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a2)
  | Original_LF__DOT__Imp_LF_Imp_AExp_aexp.AMult a1 a2 => Nat_mul (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a1) (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a2)

-- test_aeval1 (Admitted)
axiom Original_LF__DOT__Imp_LF_Imp_AExp_test__aeval1 : Corelib_Init_Logic_eq 
  (Original_LF__DOT__Imp_LF_Imp_AExp_aeval (Original_LF__DOT__Imp_LF_Imp_AExp_APlus (Original_LF__DOT__Imp_LF_Imp_AExp_ANum (nat.S (nat.S nat.O))) (Original_LF__DOT__Imp_LF_Imp_AExp_ANum (nat.S (nat.S nat.O))))) 
  (nat.S (nat.S (nat.S (nat.S nat.O))))

-- ============================================================
-- Original.LF.Rel admitted theorem
-- ============================================================

-- total_relation_not_partial_function (Admitted)
axiom Original_LF_Rel_total__relation__not__partial__function : (Original_LF_Rel_partial__function Original_LF_Rel_total__relation) → MyFalse

-- ============================================================
-- Original.LF_DOT_AltAuto definitions
-- ============================================================

-- eq_example3: nil = cons x l -> False
def Original_LF__DOT__AltAuto_LF_AltAuto_eq__example3 (X : Type) (x : X) (l : Original_LF__DOT__Poly_LF_Poly_list X)
  (H : Corelib_Init_Logic_eq (Original_LF__DOT__Poly_LF_Poly_list.nil) (Original_LF__DOT__Poly_LF_Poly_list.cons x l)) : MyFalse :=
  nomatch H

-- End of file

