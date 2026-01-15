-- Comprehensive Lean translation for IndProp isomorphisms
set_option linter.all false

-- ============================================================
-- Basic Types
-- ============================================================

-- True type
inductive TrueType : Prop where
  | I : TrueType

def TrueType_I := TrueType.I

-- False type  
inductive FalseType : Prop where

-- Original.False
def Original_False : Prop := FalseType

-- Custom bool to avoid Lean stdlib issues
inductive mybool : Type where
  | mytrue : mybool
  | myfalse : mybool

def mybool_mytrue : mybool := mybool.mytrue
def mybool_myfalse : mybool := mybool.myfalse

-- Custom nat
inductive nat : Type where
  | O : nat
  | S : nat → nat

def nat_O := nat.O
def nat_S := nat.S
def S := nat.S
def O := nat.O

-- Nat operations
def Nat_add : nat → nat → nat
  | nat.O, m => m
  | nat.S n, m => nat.S (Nat_add n m)

def Nat_sub : nat → nat → nat
  | n, nat.O => n
  | nat.O, nat.S _ => nat.O
  | nat.S n, nat.S m => Nat_sub n m

def Nat_mul : nat → nat → nat
  | nat.O, _ => nat.O
  | nat.S n, m => Nat_add m (Nat_mul n m)

def Nat_eqb : nat → nat → mybool
  | nat.O, nat.O => mybool.mytrue
  | nat.S n, nat.S m => Nat_eqb n m
  | _, _ => mybool.myfalse

def Nat_leb : nat → nat → mybool
  | nat.O, _ => mybool.mytrue
  | nat.S _, nat.O => mybool.myfalse
  | nat.S n, nat.S m => Nat_leb n m

def Nat_pred : nat → nat
  | nat.O => nat.O
  | nat.S n => n

def Nat_succ : nat → nat := nat.S

def Nat_ltb : nat → nat → mybool
  | _, nat.O => mybool.myfalse
  | nat.O, nat.S _ => mybool.mytrue
  | nat.S n, nat.S m => Nat_ltb n m

-- Bool operations
def bool_negb : mybool → mybool
  | mybool.mytrue => mybool.myfalse
  | mybool.myfalse => mybool.mytrue

def bool_andb : mybool → mybool → mybool
  | mybool.mytrue, b => b
  | mybool.myfalse, _ => mybool.myfalse

def bool_orb : mybool → mybool → mybool
  | mybool.mytrue, _ => mybool.mytrue
  | mybool.myfalse, b => b

def bool_eqb : mybool → mybool → mybool
  | mybool.mytrue, mybool.mytrue => mybool.mytrue
  | mybool.myfalse, mybool.myfalse => mybool.mytrue
  | _, _ => mybool.myfalse

-- Option type
inductive option (A : Type) : Type where
  | None : option A
  | Some : A → option A

def None := @option.None
def Some := @option.Some

-- Product type
inductive prod (A B : Type) : Type where
  | pair : A → B → prod A B

def pair := @prod.pair

-- List type
inductive list (A : Type) : Type where
  | nil : list A
  | cons : A → list A → list A

def nil := @list.nil
def cons := @list.cons

-- Or type (disjunction)
inductive or (A B : Prop) : Prop where
  | inl : A → or A B
  | inr : B → or A B

-- Logic not
def Logic_not (P : Prop) : Prop := P → FalseType

-- ============================================================
-- ASCII
-- ============================================================

inductive Ascii_ascii : Type where
  | Ascii : mybool → mybool → mybool → mybool → mybool → mybool → mybool → mybool → Ascii_ascii

def Ascii := Ascii_ascii
def Ascii_Ascii := Ascii_ascii.Ascii

-- ASCII equality
def Ascii_eqb : Ascii_ascii → Ascii_ascii → mybool
  | Ascii_ascii.Ascii a0 a1 a2 a3 a4 a5 a6 a7,
    Ascii_ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    bool_andb (bool_eqb a0 b0)
      (bool_andb (bool_eqb a1 b1)
        (bool_andb (bool_eqb a2 b2)
          (bool_andb (bool_eqb a3 b3)
            (bool_andb (bool_eqb a4 b4)
              (bool_andb (bool_eqb a5 b5)
                (bool_andb (bool_eqb a6 b6) (bool_eqb a7 b7)))))))

-- ============================================================
-- Corelib.Init.Logic.eq
-- ============================================================

inductive Corelib_Init_Logic_eq {A : Type} (x : A) : A → Prop where
  | refl : Corelib_Init_Logic_eq x x

def Corelib_Init_Logic_eq_refl {A : Type} (x : A) : Corelib_Init_Logic_eq x x :=
  Corelib_Init_Logic_eq.refl

-- Prop-level equality
inductive Corelib_Init_Logic_eq_Prop {A : Prop} (x : A) : A → Prop where
  | refl : Corelib_Init_Logic_eq_Prop x x

-- ============================================================
-- exists and iff
-- ============================================================

inductive ex {A : Type} (P : A → Prop) : Prop where
  | ex_intro : ∀ x, P x → ex P

def ex_intro := @ex.ex_intro

inductive iff (A B : Prop) : Prop where
  | mk : (A → B) → (B → A) → iff A B

def iff_intro := @iff.mk
def iff_mk := @iff.mk

-- Projections for iff
def mp {A B : Prop} : iff A B → A → B
  | iff.mk f _, a => f a

def mpr {A B : Prop} : iff A B → B → A
  | iff.mk _ g, b => g b

-- ============================================================
-- Original.LF_DOT_Basics types (bool, true, false)
-- ============================================================

inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

def Original_LF__DOT__Basics_LF_Basics_andb : Original_LF__DOT__Basics_LF_Basics_bool → Original_LF__DOT__Basics_LF_Basics_bool → Original_LF__DOT__Basics_LF_Basics_bool
  | Original_LF__DOT__Basics_LF_Basics_bool.true, b => b
  | Original_LF__DOT__Basics_LF_Basics_bool.false, _ => Original_LF__DOT__Basics_LF_Basics_bool.false

def Original_LF__DOT__Basics_LF_Basics_orb : Original_LF__DOT__Basics_LF_Basics_bool → Original_LF__DOT__Basics_LF_Basics_bool → Original_LF__DOT__Basics_LF_Basics_bool
  | Original_LF__DOT__Basics_LF_Basics_bool.true, _ => Original_LF__DOT__Basics_LF_Basics_bool.true
  | Original_LF__DOT__Basics_LF_Basics_bool.false, b => b

-- ============================================================
-- Original.LF_DOT_Poly types (list, nil, cons, app)
-- ============================================================

inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

def Original_LF__DOT__Poly_LF_Poly_cons {X : Type} (x : X) (l : Original_LF__DOT__Poly_LF_Poly_list X) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons x l

def Original_LF__DOT__Poly_LF_Poly_app (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X
  | Original_LF__DOT__Poly_LF_Poly_list.nil, l2 => l2
  | Original_LF__DOT__Poly_LF_Poly_list.cons x l1, l2 => Original_LF__DOT__Poly_LF_Poly_list.cons x (Original_LF__DOT__Poly_LF_Poly_app X l1 l2)

-- ============================================================
-- Original.LF_DOT_IndProp types (reg_exp)
-- ============================================================

inductive Original_LF__DOT__IndProp_LF_IndProp_reg__exp (T : Type) : Type where
  | EmptySet : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | EmptyStr : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Char : T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | App : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Union : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Star : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T

-- Constructor aliases
def Original_LF__DOT__IndProp_LF_IndProp_EmptySet (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptySet

def Original_LF__DOT__IndProp_LF_IndProp_EmptyStr (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptyStr

def Original_LF__DOT__IndProp_LF_IndProp_Char {T : Type} (t : T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Char t

def Original_LF__DOT__IndProp_LF_IndProp_App {T : Type} (r1 r2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.App r1 r2

def Original_LF__DOT__IndProp_LF_IndProp_Union {T : Type} (r1 r2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Union r1 r2

def Original_LF__DOT__IndProp_LF_IndProp_Star {T : Type} (r : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star r

-- ============================================================
-- exp_match
-- ============================================================

inductive Original_LF__DOT__IndProp_LF_IndProp_exp__match {T : Type} : Original_LF__DOT__Poly_LF_Poly_list T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Prop where
  | MEmpty : Original_LF__DOT__IndProp_LF_IndProp_exp__match .nil .EmptyStr
  | MChar (x : T) : Original_LF__DOT__IndProp_LF_IndProp_exp__match (.cons x .nil) (.Char x)
  | MApp (s1 s2 : Original_LF__DOT__Poly_LF_Poly_list T) (re1 re2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
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

-- Aliases for exp_match
def Original_LF__DOT__IndProp_LF_IndProp_EmptyStr' (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_nil T) (Original_LF__DOT__IndProp_LF_IndProp_EmptyStr T) :=
  Original_LF__DOT__IndProp_LF_IndProp_exp__match.MEmpty

-- ============================================================
-- reflect
-- ============================================================

inductive Original_LF__DOT__IndProp_LF_IndProp_reflect (P : Prop) : Original_LF__DOT__Basics_LF_Basics_bool → Prop where
  | ReflectT : P → Original_LF__DOT__IndProp_LF_IndProp_reflect P Original_LF__DOT__Basics_LF_Basics_bool.true
  | ReflectF : Logic_not P → Original_LF__DOT__IndProp_LF_IndProp_reflect P Original_LF__DOT__Basics_LF_Basics_bool.false

-- ============================================================
-- ASCII character c (99 = 0b01100011)
-- In Coq's Ascii, bits are stored LSB first
-- 99 = 64 + 32 + 2 + 1 = bits: 1 1 0 0 0 1 1 0 (LSB first)
-- ============================================================

def Original_LF__DOT__IndProp_LF_IndProp_c : Ascii_ascii :=
  Ascii_ascii.Ascii mybool.mytrue mybool.mytrue mybool.myfalse mybool.myfalse mybool.myfalse mybool.mytrue mybool.mytrue mybool.myfalse

-- ============================================================
-- List_In (standard library In)
-- ============================================================

def List_In {A : Type} (x : A) : list A → Prop
  | .nil => FalseType
  | .cons x' l' => or (Corelib_Init_Logic_eq x' x) (List_In x l')

-- ============================================================
-- RecallIn.In - this is actually defined, not admitted
-- ============================================================

def Original_LF__DOT__IndProp_LF_IndProp_RecallIn_In (A : Type) (x : A) : Original_LF__DOT__Poly_LF_Poly_list A → Prop
  | .nil => FalseType
  | .cons x' l' => or (Corelib_Init_Logic_eq x' x) (Original_LF__DOT__IndProp_LF_IndProp_RecallIn_In A x l')

-- Reduction equations for RecallIn.In
theorem Original_LF__DOT__IndProp_LF_IndProp_RecallIn_In_nil (A : Type) (x : A) :
  Original_LF__DOT__IndProp_LF_IndProp_RecallIn_In A x (Original_LF__DOT__Poly_LF_Poly_list.nil) = FalseType := rfl

theorem Original_LF__DOT__IndProp_LF_IndProp_RecallIn_In_cons (A : Type) (x x' : A) (l' : Original_LF__DOT__Poly_LF_Poly_list A) :
  Original_LF__DOT__IndProp_LF_IndProp_RecallIn_In A x (Original_LF__DOT__Poly_LF_Poly_list.cons x' l') = 
  or (Corelib_Init_Logic_eq x' x) (Original_LF__DOT__IndProp_LF_IndProp_RecallIn_In A x l') := rfl

-- ============================================================
-- match_eps (Admitted in Original.v)
-- ============================================================

axiom Original_LF__DOT__IndProp_LF_IndProp_match__eps :
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp Ascii_ascii → Original_LF__DOT__Basics_LF_Basics_bool

-- ============================================================
-- derive (Admitted in Original.v)
-- ============================================================

axiom Original_LF__DOT__IndProp_LF_IndProp_derive :
  Ascii_ascii → Original_LF__DOT__IndProp_LF_IndProp_reg__exp Ascii_ascii → Original_LF__DOT__IndProp_LF_IndProp_reg__exp Ascii_ascii

-- ============================================================
-- re_not_empty (Admitted in Original.v)
-- ============================================================

axiom Original_LF__DOT__IndProp_LF_IndProp_re__not__empty :
  ∀ {T : Type}, Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__Basics_LF_Basics_bool

-- ============================================================
-- refl_matches_eps - definition for the type
-- ============================================================

def Original_LF__DOT__IndProp_LF_IndProp_refl__matches__eps 
  (matches_eps : Original_LF__DOT__IndProp_LF_IndProp_reg__exp Ascii_ascii → Original_LF__DOT__Basics_LF_Basics_bool) : Prop :=
  ∀ (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp Ascii_ascii),
    Original_LF__DOT__IndProp_LF_IndProp_reflect 
      (Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_nil Ascii_ascii) re) 
      (matches_eps re)

-- ============================================================
-- match_eps_refl (Admitted in Original.v)
-- ============================================================

axiom Original_LF__DOT__IndProp_LF_IndProp_match__eps__refl :
  Original_LF__DOT__IndProp_LF_IndProp_refl__matches__eps Original_LF__DOT__IndProp_LF_IndProp_match__eps

-- ============================================================
-- re_not_empty_correct (Admitted in Original.v)
-- ============================================================

axiom Original_LF__DOT__IndProp_LF_IndProp_re__not__empty__correct :
  ∀ (T : Type) (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T),
    iff (ex (fun s => Original_LF__DOT__IndProp_LF_IndProp_exp__match s re))
        (Corelib_Init_Logic_eq (Original_LF__DOT__IndProp_LF_IndProp_re__not__empty re) Original_LF__DOT__Basics_LF_Basics_bool.true)

-- ============================================================
-- test_der4 (Admitted in Original.v)
-- ============================================================

axiom Original_LF__DOT__IndProp_LF_IndProp_test__der4 :
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__IndProp_LF_IndProp_match__eps 
      (Original_LF__DOT__IndProp_LF_IndProp_derive Original_LF__DOT__IndProp_LF_IndProp_c 
        (Original_LF__DOT__IndProp_LF_IndProp_App 
          (Original_LF__DOT__IndProp_LF_IndProp_EmptyStr Ascii_ascii)
          (Original_LF__DOT__IndProp_LF_IndProp_Char Original_LF__DOT__IndProp_LF_IndProp_c))))
    Original_LF__DOT__Basics_LF_Basics_bool.true
