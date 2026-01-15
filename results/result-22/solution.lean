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

-- PeanoNat.Nat.add is just Nat_add
def PeanoNat_Nat_add : nat → nat → nat := Nat_add

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

-- and (conjunction)
inductive and (A B : Prop) : Prop where
  | intro : A → B → and A B

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

-- even
def Original_LF__DOT__Basics_LF_Basics_even : nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O => Original_LF__DOT__Basics_LF_Basics_bool.true
  | nat.S nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S (nat.S n') => Original_LF__DOT__Basics_LF_Basics_even n'

-- leb (less-than-or-equal for Basics bool)
def Original_LF__DOT__Basics_LF_Basics_leb : nat → nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O, _ => Original_LF__DOT__Basics_LF_Basics_bool.true
  | nat.S _, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S n', nat.S m' => Original_LF__DOT__Basics_LF_Basics_leb n' m'

-- le (less-than-or-equal on nat)
inductive le (n : nat) : nat → Prop where
  | le_n : le n n
  | le_S (m : nat) : le n m → le n (nat.S m)

-- ============================================================
-- Original.LF_DOT_Induction definitions
-- ============================================================

-- double
def Original_LF__DOT__Induction_LF_Induction_double : nat → nat
  | nat.O => nat.O
  | nat.S n' => nat.S (nat.S (Original_LF__DOT__Induction_LF_Induction_double n'))

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

-- map for poly list
def Original_LF__DOT__Poly_LF_Poly_map (X Y : Type) (f : X → Y) : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list Y
  | Original_LF__DOT__Poly_LF_Poly_list.nil => Original_LF__DOT__Poly_LF_Poly_list.nil
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t => Original_LF__DOT__Poly_LF_Poly_list.cons (f h) (Original_LF__DOT__Poly_LF_Poly_map X Y f t)

-- ============================================================
-- Original.LF_DOT_Logic definitions
-- ============================================================

-- In predicate for Logic
def Original_LF__DOT__Logic_LF_Logic_In (A : Type) (x : A) : Original_LF__DOT__Poly_LF_Poly_list A → Prop
  | Original_LF__DOT__Poly_LF_Poly_list.nil => MyFalse
  | Original_LF__DOT__Poly_LF_Poly_list.cons x' l' => Corelib_Init_Logic_eq x' x ∨ Original_LF__DOT__Logic_LF_Logic_In A x l'

-- Even predicate for Logic (inductive)
inductive Original_LF__DOT__Logic_LF_Logic_Even : nat → Prop where
  | Even_0 : Original_LF__DOT__Logic_LF_Logic_Even nat.O
  | Even_SS (n : nat) (H : Original_LF__DOT__Logic_LF_Logic_Even n) : Original_LF__DOT__Logic_LF_Logic_Even (nat.S (nat.S n))

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
-- Original.LF_DOT_Lists.LF.Lists.NatList definitions
-- ============================================================

-- natlist type (custom list of nats)
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natlist : Type where
  | nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist

-- natlist constructors
def Original_LF__DOT__Lists_LF_Lists_NatList_nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil

def Original_LF__DOT__Lists_LF_Lists_NatList_cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons

-- bag is a type alias
def Original_LF__DOT__Lists_LF_Lists_NatList_bag : Type := Original_LF__DOT__Lists_LF_Lists_NatList_natlist

-- length
def Original_LF__DOT__Lists_LF_Lists_NatList_length : Original_LF__DOT__Lists_LF_Lists_NatList_natlist → nat
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil => nat.O
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons _ t => nat.S (Original_LF__DOT__Lists_LF_Lists_NatList_length t)

-- app
def Original_LF__DOT__Lists_LF_Lists_NatList_app : Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil, l2 => l2
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h t, l2 => Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h (Original_LF__DOT__Lists_LF_Lists_NatList_app t l2)

-- rev
def Original_LF__DOT__Lists_LF_Lists_NatList_rev : Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil => Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h t =>
      Original_LF__DOT__Lists_LF_Lists_NatList_app (Original_LF__DOT__Lists_LF_Lists_NatList_rev t)
        (Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil)

-- count is admitted (axiom) in the original Rocq code
axiom Original_LF__DOT__Lists_LF_Lists_NatList_count : nat → Original_LF__DOT__Lists_LF_Lists_NatList_bag → nat

-- remove_one is admitted (axiom) in the original Rocq code
axiom Original_LF__DOT__Lists_LF_Lists_NatList_remove__one : nat → Original_LF__DOT__Lists_LF_Lists_NatList_bag → Original_LF__DOT__Lists_LF_Lists_NatList_bag

-- test_remove_one3: count 4 (remove_one 5 [2;1;4;5;1;4]) = 2
axiom Original_LF__DOT__Lists_LF_Lists_NatList_test__remove__one3 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_count 
       (S (S (S (S _0))))  -- 4
       (Original_LF__DOT__Lists_LF_Lists_NatList_remove__one 
          (S (S (S (S (S _0)))))  -- 5
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S _0))  -- 2
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)  -- 1
                (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S _0))))  -- 4
                   (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S (S _0)))))  -- 5
                      (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)  -- 1
                         (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S _0))))  -- 4
                            Original_LF__DOT__Lists_LF_Lists_NatList_nil))))))))
    (S (S _0))  -- 2

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
-- Option type
-- ============================================================

inductive option (A : Type) : Type where
  | None : option A
  | Some : A → option A

def None {A : Type} : option A := option.None
def Some {A : Type} (a : A) : option A := option.Some a

-- ============================================================
-- List.In
-- ============================================================

def List_In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | list.nil => MyFalse
  | list.cons x' l' => Corelib_Init_Logic_eq x' x ∨ List_In x l'

-- ============================================================
-- Relation and clos_refl_trans_1n (for LF.Rel)
-- ============================================================

def Original_LF_Rel_relation (X : Type) := X → X → Prop

inductive Original_LF_Rel_clos__refl__trans__1n {A : Type} (R : A → A → Prop) : A → A → Prop where
  | rt1n_refl (x : A) : Original_LF_Rel_clos__refl__trans__1n R x x
  | rt1n_trans (x y z : A) (Hxy : R x y) (Hrest : Original_LF_Rel_clos__refl__trans__1n R y z) : Original_LF_Rel_clos__refl__trans__1n R x z

-- ============================================================
-- Original.LF_DOT_Logic definitions
-- ============================================================

-- not_true_iff_false: b <> true <-> b = false
-- This is Admitted in Original.v, so we use axiom
axiom Original_LF__DOT__Logic_LF_Logic_not__true__iff__false :
  ∀ (b : Original_LF__DOT__Basics_LF_Basics_bool), iff 
    (Corelib_Init_Logic_eq b Original_LF__DOT__Basics_LF_Basics_true → MyFalse)
    (Corelib_Init_Logic_eq b Original_LF__DOT__Basics_LF_Basics_false)

-- function_equality_ex1: plus 3 = plus (pred 4)
-- This is Admitted in Original.v
axiom Original_LF__DOT__Logic_LF_Logic_function__equality__ex1 :
  Corelib_Init_Logic_eq (Nat_add (S (S (S _0)))) (Nat_add (Nat_pred (S (S (S (S _0))))))

-- ============================================================
-- Admitted theorems from LF.Rel
-- ============================================================

-- rsc_R: R x y -> clos_refl_trans_1n R x y
axiom Original_LF_Rel_rsc__R {X : Type} (R : X → X → Prop) (x y : X) :
  R x y → Original_LF_Rel_clos__refl__trans__1n R x y

-- ============================================================
-- Admitted theorems from LF_DOT_AltAuto
-- ============================================================

-- silly1: 1 + n = S n (Admitted in Original.v)
axiom Original_LF__DOT__AltAuto_LF_AltAuto_silly1 (n : nat) :
  Corelib_Init_Logic_eq (Nat_add (S _0) n) (S n)

-- le_antisym: (n <= m /\ m <= n) -> n = m (Admitted in Original.v)
axiom Original_LF__DOT__AltAuto_LF_AltAuto_le__antisym (n m : nat) :
  and (le n m) (le m n) → Corelib_Init_Logic_eq n m

-- ============================================================
-- Admitted theorems from LF_DOT_Auto
-- ============================================================

-- auto_example_6 (Admitted in Original.v)
axiom Original_LF__DOT__Auto_LF_Auto_auto__example__6 (n m p : nat) :
  (le n p → and (le n m) (le m n)) → le n p → Corelib_Init_Logic_eq n m

-- ============================================================
-- Definitions from LF_DOT_ImpCEvalFun
-- ============================================================

-- ceval_step2 is a Fixpoint: state -> com -> nat -> state
-- Since it's a recursive function and we just need the type, use axiom
def Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step2 : 
    Original_LF__DOT__Imp_LF_Imp_state → Original_LF__DOT__Imp_LF_Imp_com → nat → Original_LF__DOT__Imp_LF_Imp_state
  | _, _, nat.O => Original_LF__DOT__Imp_LF_Imp_empty__st
  | st, Original_LF__DOT__Imp_LF_Imp_com.CSkip, nat.S _ => st
  | st, Original_LF__DOT__Imp_LF_Imp_com.CAsgn l a1, nat.S _ =>
      Original_LF__DOT__Maps_LF_Maps_t__update nat st l (Original_LF__DOT__Imp_LF_Imp_aeval st a1)
  | st, Original_LF__DOT__Imp_LF_Imp_com.CSeq c1 c2, nat.S i' =>
      let st' := Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step2 st c1 i'
      Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step2 st' c2 i'
  | st, Original_LF__DOT__Imp_LF_Imp_com.CIf b c1 c2, nat.S i' =>
      match Original_LF__DOT__Imp_LF_Imp_beval st b with
      | Stdlib_bool.true => Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step2 st c1 i'
      | Stdlib_bool.false => Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step2 st c2 i'
  | st, Original_LF__DOT__Imp_LF_Imp_com.CWhile b c1, nat.S i' =>
      match Original_LF__DOT__Imp_LF_Imp_beval st b with
      | Stdlib_bool.true =>
          let st' := Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step2 st c1 i'
          Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step2 st' (Original_LF__DOT__Imp_LF_Imp_com.CWhile b c1) i'
      | Stdlib_bool.false => st

-- ============================================================
-- Admitted theorems from LF_DOT_Imp.AExp
-- ============================================================

-- silly_presburger_example: m + n <= n + o /\ o + 3 = p + 3 -> m <= p (Admitted in Original.v)
axiom Original_LF__DOT__Imp_LF_Imp_AExp_silly__presburger__example (m n o p : nat) :
  and (le (PeanoNat_Nat_add m n) (PeanoNat_Nat_add n o))
      (Corelib_Init_Logic_eq (PeanoNat_Nat_add o (S (S (S _0)))) (PeanoNat_Nat_add p (S (S (S _0))))) →
  le m p

-- ============================================================
-- Admitted theorems from LF_DOT_IndProp
-- ============================================================

-- leb_iff: n <=? m = true <-> n <= m (Admitted in Original.v)
-- Uses Original_LF__DOT__Basics_LF_Basics_leb and Original_LF__DOT__Basics_LF_Basics_true
axiom Original_LF__DOT__IndProp_LF_IndProp_leb__iff (n m : nat) :
  iff (Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_leb n m) Original_LF__DOT__Basics_LF_Basics_true) (le n m)

-- not_equiv_false: ~P -> (P <-> False) (Admitted in Original.v)
-- The signature expected by the isomorphism is: forall P, (P -> False) -> (P <-> Original.False)
axiom Original_LF__DOT__IndProp_LF_IndProp_not__equiv__false (P : Prop) :
  (P → Original_False) → iff P Original_False

-- ============================================================
-- Admitted theorems from LF_DOT_Lists.NatList
-- ============================================================

-- rev_length (Admitted in Original.v)
axiom Original_LF__DOT__Lists_LF_Lists_NatList_rev__length (l : Original_LF__DOT__Lists_LF_Lists_NatList_natlist) :
  Corelib_Init_Logic_eq (Original_LF__DOT__Lists_LF_Lists_NatList_length (Original_LF__DOT__Lists_LF_Lists_NatList_rev l)) (Original_LF__DOT__Lists_LF_Lists_NatList_length l)

-- ============================================================
-- Admitted theorems from LF_DOT_Logic
-- ============================================================

-- even_bool_prop (Admitted in Original.v)
axiom Original_LF__DOT__Logic_LF_Logic_even__bool__prop (n : nat) :
  iff (Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_even n) Original_LF__DOT__Basics_LF_Basics_true) (Original_LF__DOT__Logic_LF_Logic_Even n)

-- lemma_application_ex: forall n ns, In n (map (fun m => m * 0) ns) -> n = 0 (Admitted in Original.v)
axiom Original_LF__DOT__Logic_LF_Logic_lemma__application__ex (n : nat) (ns : Original_LF__DOT__Poly_LF_Poly_list nat) :
  Original_LF__DOT__Logic_LF_Logic_In nat n (Original_LF__DOT__Poly_LF_Poly_map nat nat (fun m => Nat_mul m _0) ns) →
  Corelib_Init_Logic_eq n _0

-- ============================================================
-- Admitted theorems from LF_DOT_Tactics
-- ============================================================

-- injection_ex1: forall n m o, [n;m] = [o;o] -> n = m (Admitted in Original.v)
axiom Original_LF__DOT__Tactics_LF_Tactics_injection__ex1 (n m o : nat) :
  Corelib_Init_Logic_eq (Original_LF__DOT__Poly_LF_Poly_cons nat n (Original_LF__DOT__Poly_LF_Poly_cons nat m (Original_LF__DOT__Poly_LF_Poly_nil nat)))
    (Original_LF__DOT__Poly_LF_Poly_cons nat o (Original_LF__DOT__Poly_LF_Poly_cons nat o (Original_LF__DOT__Poly_LF_Poly_nil nat))) →
  Corelib_Init_Logic_eq n m

-- ============================================================
-- Additional Types for disc_fn and list'
-- ============================================================

-- Original.True (separate from Corelib/MyTrue)
inductive Original_True : Prop where
  | I : Original_True

def Original_True_I := Original_True.I

-- list' (alternative list definition from LF.Poly)
inductive Original_LF__DOT__Poly_LF_Poly_list' (X : Type) : Type where
  | nil' : Original_LF__DOT__Poly_LF_Poly_list' X
  | cons' : X → Original_LF__DOT__Poly_LF_Poly_list' X → Original_LF__DOT__Poly_LF_Poly_list' X

def Original_LF__DOT__Poly_LF_Poly_list'_nil' (X : Type) : Original_LF__DOT__Poly_LF_Poly_list' X :=
  Original_LF__DOT__Poly_LF_Poly_list'.nil'

def Original_LF__DOT__Poly_LF_Poly_list'_cons' (X : Type) (x : X) (xs : Original_LF__DOT__Poly_LF_Poly_list' X) : Original_LF__DOT__Poly_LF_Poly_list' X :=
  Original_LF__DOT__Poly_LF_Poly_list'.cons' x xs

-- disc_fn (discriminating function from LF.Logic)
-- disc_fn n := match n with | O => True | S _ => False end
def Original_LF__DOT__Logic_LF_Logic_disc__fn : nat → Prop
  | nat.O => Original_True
  | nat.S _ => Original_False

-- ============================================================
-- AltAuto definitions (Admitted theorems)
-- ============================================================

-- auto_example_1' : forall P Q R, (P -> Q) -> (Q -> R) -> P -> R (Admitted)
axiom Original_LF__DOT__AltAuto_LF_AltAuto_auto__example__1' (P Q R : Prop) :
  (P → Q) → (Q → R) → P → R

-- false_assumed' : False -> 0 = 1 (Admitted)
axiom Original_LF__DOT__AltAuto_LF_AltAuto_false__assumed' :
  Original_False → Corelib_Init_Logic_eq _0 (S _0)

-- intuition_simplify2' : forall x y (P Q : nat -> Prop), x = y /\ (P x -> Q x) /\ P x -> Q y (Admitted)
axiom Original_LF__DOT__AltAuto_LF_AltAuto_intuition__simplify2' (x y : nat) (P Q : nat → Prop) :
  and (Corelib_Init_Logic_eq x y) (and (P x → Q x) (P x)) → Q y

-- ============================================================
-- Auto definitions (Admitted theorems)
-- ============================================================

-- silly2_eassumption : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
--   (exists y, P 42 y) -> (forall x y, P x y -> Q x) -> Q 42 (Admitted)
axiom Original_LF__DOT__Auto_LF_Auto_silly2__eassumption (P : nat → nat → Prop) (Q : nat → Prop) :
  ex (fun y => P (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S _0)))))))))))))))))))))))))))))))))))))))))) y) →
  (∀ x y : nat, P x y → Q x) →
  Q (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S _0))))))))))))))))))))))))))))))))))))))))))

-- ============================================================
-- Induction definitions (Admitted theorems)
-- ============================================================

-- mult_1_l : forall n, 1 * n = n (Admitted)
axiom Original_LF__DOT__Induction_LF_Induction_mult__1__l (n : nat) :
  Corelib_Init_Logic_eq (Nat_mul (S _0) n) n

-- mul_comm : forall m n, m * n = n * m (Admitted)
axiom Original_LF__DOT__Induction_LF_Induction_mul__comm (m n : nat) :
  Corelib_Init_Logic_eq (Nat_mul m n) (Nat_mul n m)

-- ============================================================
-- IndPrinciples definitions (Admitted theorems)
-- ============================================================

-- mul_0_r' : forall n, n * 0 = 0 (Admitted)
axiom Original_LF__DOT__IndPrinciples_LF_IndPrinciples_mul__0__r' (n : nat) :
  Corelib_Init_Logic_eq (Nat_mul n _0) _0

-- ============================================================
-- Logic definitions (Admitted theorems)
-- ============================================================

-- and_commut : forall P Q, P /\ Q -> Q /\ P (Admitted)
axiom Original_LF__DOT__Logic_LF_Logic_and__commut (P Q : Prop) :
  and P Q → and Q P

-- ============================================================
-- Imp definitions
-- ============================================================

-- W : string (a variable name)
def Original_LF__DOT__Imp_LF_Imp_W : String_string :=
  String_String (Ascii_Ascii Stdlib_bool.true Stdlib_bool.true Stdlib_bool.true Stdlib_bool.false Stdlib_bool.true Stdlib_bool.false Stdlib_bool.true Stdlib_bool.false) String_EmptyString

-- add_assoc__lia : forall n m p, n + (m + p) = n + m + p (Admitted)
axiom Original_LF__DOT__Imp_LF_Imp_AExp_add__assoc____lia (n m p : nat) :
  Corelib_Init_Logic_eq (Nat_add n (Nat_add m p)) (Nat_add (Nat_add n m) p)

-- ============================================================
-- Maps definitions (Admitted theorems)
-- ============================================================

-- example_empty := (_ !-> false) = t_empty false
-- This is a value of type total_map bool
def Original_LF__DOT__Maps_LF_Maps_example__empty : Original_LF__DOT__Maps_LF_Maps_total__map Stdlib_bool :=
  Original_LF__DOT__Maps_LF_Maps_t__empty Stdlib_bool Stdlib_bool.false

-- ============================================================
-- ProofObjects definitions (Admitted theorems)
-- ============================================================

-- and_comm : forall P Q, P /\ Q <-> Q /\ P (Admitted)
axiom Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_And_and__comm (P Q : Prop) :
  iff (and P Q) (and Q P)

