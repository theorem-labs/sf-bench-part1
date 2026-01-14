-- Comprehensive Lean translation for all required isomorphisms
set_option autoImplicit false
set_option linter.unusedVariables false

-- ==================== Basic Types ====================

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Nat addition
def Nat_add : nat → nat → nat
  | nat.O, m => m
  | nat.S n, m => nat.S (Nat_add n m)

-- ==================== Logic Types ====================

-- True in Prop (will become SProp when imported)
-- Named PTrue to avoid conflict with Lean's builtin True
inductive PTrue : Prop where
  | intro : PTrue

-- False in Prop (empty type)
inductive MyFalse : Prop where

-- Logic.not definition
def Logic_not (P : Prop) : Prop := P → MyFalse

-- Equality in Prop (will become SProp when imported)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality for Prop arguments (needed for Corelib_Init_Logic_eq_Prop isomorphism)
def Corelib_Init_Logic_eq_Prop (A : Prop) (x y : A) : Prop := PTrue

-- And (conjunction)
structure «and» (A B : Prop) : Prop where
  intro ::
  left : A
  right : B

-- Iff (biconditional)
structure iff (A B : Prop) : Prop where
  mp : A → B
  mpr : B → A

-- Existential
inductive ex {A : Type} (P : A → Prop) : Prop where
  | intro (x : A) (h : P x) : ex P

-- ==================== Bool Types ====================

-- Standard bool for Stdlib.Init.Datatypes.bool (used by Ascii)
inductive Stdlib_bool : Type where
  | true : Stdlib_bool
  | false : Stdlib_bool

-- Bool for Original.LF_DOT_Basics.LF.Basics.bool
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | Original_LF__DOT__Basics_LF_Basics_bool_true : Original_LF__DOT__Basics_LF_Basics_bool
  | Original_LF__DOT__Basics_LF_Basics_bool_false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.Original_LF__DOT__Basics_LF_Basics_bool_true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.Original_LF__DOT__Basics_LF_Basics_bool_false

-- ==================== Ascii and String ====================

-- Ascii type (8 booleans)
inductive Ascii_ascii : Type where
  | Ascii : Stdlib_bool → Stdlib_bool → Stdlib_bool → Stdlib_bool →
            Stdlib_bool → Stdlib_bool → Stdlib_bool → Stdlib_bool → Ascii_ascii

-- String.string type
inductive String_string : Type where
  | EmptyString : String_string
  | String : Ascii_ascii → String_string → String_string

-- ==================== Polymorphic List ====================

-- Original.LF_DOT_Poly.LF.Poly.list
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

def Original_LF__DOT__Poly_LF_Poly_cons {X : Type} : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons

-- app function for polymorphic list
def Original_LF__DOT__Poly_LF_Poly_app {X : Type} : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X
  | .nil, l2 => l2
  | .cons h t, l2 => .cons h (Original_LF__DOT__Poly_LF_Poly_app t l2)

-- ==================== NatList ====================

-- Original.LF_DOT_Lists.LF.Lists.NatList.natlist
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natlist : Type where
  | nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist

def Original_LF__DOT__Lists_LF_Lists_NatList_nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil

def Original_LF__DOT__Lists_LF_Lists_NatList_cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons

-- ==================== Maps ====================

-- Original.LF_DOT_Maps.LF.Maps.total_map
def Original_LF__DOT__Maps_LF_Maps_total__map (A : Type) : Type :=
  String_string → A

-- t_update for total_map
def Original_LF__DOT__Maps_LF_Maps_t__update {A : Type}
    (m : Original_LF__DOT__Maps_LF_Maps_total__map A)
    (x : String_string)
    (v : A) : Original_LF__DOT__Maps_LF_Maps_total__map A :=
  fun x' => if stringEq x x' then v else m x'
where
  stringEq : String_string → String_string → Bool
    | .EmptyString, .EmptyString => true
    | .String a1 s1, .String a2 s2 => asciiEq a1 a2 && stringEq s1 s2
    | _, _ => false
  asciiEq : Ascii_ascii → Ascii_ascii → Bool
    | .Ascii b0 b1 b2 b3 b4 b5 b6 b7, .Ascii c0 c1 c2 c3 c4 c5 c6 c7 =>
      boolEq b0 c0 && boolEq b1 c1 && boolEq b2 c2 && boolEq b3 c3 &&
      boolEq b4 c4 && boolEq b5 c5 && boolEq b6 c6 && boolEq b7 c7
  boolEq : Stdlib_bool → Stdlib_bool → Bool
    | .true, .true => true
    | .false, .false => true
    | _, _ => false

-- ==================== Imp Definitions ====================

-- state := total_map nat
def Original_LF__DOT__Imp_LF_Imp_state : Type :=
  Original_LF__DOT__Maps_LF_Maps_total__map nat

-- aexp
inductive Original_LF__DOT__Imp_LF_Imp_aexp : Type where
  | ANum : nat → Original_LF__DOT__Imp_LF_Imp_aexp
  | AId : String_string → Original_LF__DOT__Imp_LF_Imp_aexp
  | APlus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp
  | AMinus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp
  | AMult : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp

-- bexp
inductive Original_LF__DOT__Imp_LF_Imp_bexp : Type where
  | BTrue : Original_LF__DOT__Imp_LF_Imp_bexp
  | BFalse : Original_LF__DOT__Imp_LF_Imp_bexp
  | BEq : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BNeq : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BLe : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BGt : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BNot : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BAnd : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp

-- com
inductive Original_LF__DOT__Imp_LF_Imp_com : Type where
  | CSkip : Original_LF__DOT__Imp_LF_Imp_com
  | CAsgn : String_string → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_com
  | CSeq : Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com
  | CIf : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com
  | CWhile : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com

-- Nat operations for aeval/beval
def nat_sub : nat → nat → nat
  | n, nat.O => n
  | nat.O, nat.S _ => nat.O
  | nat.S n, nat.S m => nat_sub n m

def nat_mul : nat → nat → nat
  | nat.O, _ => nat.O
  | nat.S n, m => Nat_add m (nat_mul n m)

def nat_eqb : nat → nat → Stdlib_bool
  | nat.O, nat.O => Stdlib_bool.true
  | nat.O, nat.S _ => Stdlib_bool.false
  | nat.S _, nat.O => Stdlib_bool.false
  | nat.S n, nat.S m => nat_eqb n m

def nat_leb : nat → nat → Stdlib_bool
  | nat.O, _ => Stdlib_bool.true
  | nat.S _, nat.O => Stdlib_bool.false
  | nat.S n, nat.S m => nat_leb n m

def negb : Stdlib_bool → Stdlib_bool
  | Stdlib_bool.true => Stdlib_bool.false
  | Stdlib_bool.false => Stdlib_bool.true

def andb : Stdlib_bool → Stdlib_bool → Stdlib_bool
  | Stdlib_bool.true, b2 => b2
  | Stdlib_bool.false, _ => Stdlib_bool.false

-- aeval
def Original_LF__DOT__Imp_LF_Imp_aeval :
    Original_LF__DOT__Imp_LF_Imp_state → Original_LF__DOT__Imp_LF_Imp_aexp → nat
  | _st, .ANum n => n
  | st, .AId x => st x
  | st, .APlus a1 a2 => Nat_add (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
  | st, .AMinus a1 a2 => nat_sub (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
  | st, .AMult a1 a2 => nat_mul (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)

-- beval
def Original_LF__DOT__Imp_LF_Imp_beval :
    Original_LF__DOT__Imp_LF_Imp_state → Original_LF__DOT__Imp_LF_Imp_bexp → Stdlib_bool
  | _st, .BTrue => Stdlib_bool.true
  | _st, .BFalse => Stdlib_bool.false
  | st, .BEq a1 a2 => nat_eqb (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
  | st, .BNeq a1 a2 => negb (nat_eqb (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2))
  | st, .BLe a1 a2 => nat_leb (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
  | st, .BGt a1 a2 => negb (nat_leb (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2))
  | st, .BNot b1 => negb (Original_LF__DOT__Imp_LF_Imp_beval st b1)
  | st, .BAnd b1 b2 => andb (Original_LF__DOT__Imp_LF_Imp_beval st b1) (Original_LF__DOT__Imp_LF_Imp_beval st b2)

-- ==================== Regular Expressions ====================

-- Original.LF_DOT_IndProp.LF.IndProp.reg_exp
inductive Original_LF__DOT__IndProp_LF_IndProp_reg__exp (T : Type) : Type where
  | EmptySet : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | EmptyStr : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Char : T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | App : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Union : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Star : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T

-- EmptySet constructor
def Original_LF__DOT__IndProp_LF_IndProp_EmptySet (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptySet

-- EmptyStr constructor
def Original_LF__DOT__IndProp_LF_IndProp_EmptyStr (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptyStr

-- Char constructor
def Original_LF__DOT__IndProp_LF_IndProp_Char {T : Type} (t : T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Char t

-- App constructor
def Original_LF__DOT__IndProp_LF_IndProp_App {T : Type} (r1 r2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.App r1 r2

-- Union constructor
def Original_LF__DOT__IndProp_LF_IndProp_Union {T : Type} (r1 r2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Union r1 r2

-- Star constructor
def Original_LF__DOT__IndProp_LF_IndProp_Star {T : Type} (r : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star r

-- ==================== le (less than or equal) ====================

-- Boolean less-than-or-equal
inductive RocqBool : Type where
  | false : RocqBool
  | true : RocqBool

def RocqBool_false : RocqBool := RocqBool.false
def RocqBool_true : RocqBool := RocqBool.true

def nat_le : nat → nat → RocqBool
  | nat.O, _ => RocqBool.true
  | nat.S _, nat.O => RocqBool.false
  | nat.S n, nat.S m => nat_le n m

-- Equality for RocqBool (needed for le definition)
inductive RocqEq {A : Type} : A → A → Prop where
  | refl (a : A) : RocqEq a a

def RocqEq_refl {A : Type} (a : A) : RocqEq a a := RocqEq.refl a

-- le as Prop
def le (n m : nat) : Prop := RocqEq (nat_le n m) RocqBool.true

-- ==================== Original.False (distinct from Logic.False) ====================

inductive Original_False : Prop where
