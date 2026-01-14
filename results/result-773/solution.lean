-- Comprehensive Lean 4 translation for all isomorphisms

set_option linter.unusedVariables false
set_option autoImplicit false

-- ==================== Core Types ====================

-- Boolean type (matching Rocq bool)  
inductive mybool : Type
| mytrue : mybool
| myfalse : mybool

-- Aliases
def mytrue : mybool := mybool.mytrue
def myfalse : mybool := mybool.myfalse

-- Natural numbers
inductive nat : Type
| O : nat
| S : nat → nat

-- Aliases for constructors
def _0 : nat := nat.O
def S : nat → nat := nat.S

-- ==================== Nat operations ====================

def Nat_add : nat → nat → nat
| nat.O, m => m
| nat.S n', m => nat.S (Nat_add n' m)

def Nat_mul : nat → nat → nat
| nat.O, _ => nat.O
| nat.S n', m => Nat_add m (Nat_mul n' m)

def nat_sub : nat → nat → nat
| nat.O, _ => nat.O
| n, nat.O => n
| nat.S n', nat.S m' => nat_sub n' m'

-- ==================== Logic types ====================

-- True type as Prop (exported as True)  
inductive True' : Prop
| I : True'

def True'_I : True' := True'.I

-- False type as Prop
inductive False' : Prop

-- Original.False alias
def Original_False : Prop := False'

-- Not (negation)
def Logic_not (P : Prop) : Prop := P → False'

-- And (conjunction)
structure and' (A B : Prop) : Prop where
  proj1 : A
  proj2 : B

-- Or (disjunction)
inductive or' (A B : Prop) : Prop
| inl : A → or' A B
| inr : B → or' A B

-- Iff (biconditional)
structure iff' (A B : Prop) : Prop where
  mp : A → B
  mpr : B → A

-- Existential quantifier
inductive ex' {A : Type} (P : A → Prop) : Prop
| intro : ∀ x : A, P x → ex' P

-- ==================== Equality ====================

-- Equality type in Prop (will become SProp in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop
| refl (a : A) : Corelib_Init_Logic_eq a a

-- eq for Prop (SProp in Rocq)
def Corelib_Init_Logic_eq_Prop (A : Prop) (a b : A) : Prop := True'

-- ==================== le (less than or equal) ====================

inductive le' : nat → nat → Prop
| le_n (n : nat) : le' n n
| le_S (n m : nat) : le' n m → le' n (nat.S m)

-- ==================== Lists ====================

-- Polymorphic list type (matching LF.Poly.list)
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

-- Standard list type (for List.In and general use)
inductive list' (A : Type) : Type
| nil : list' A
| cons : A → list' A → list' A

def nil' (A : Type) : list' A := list'.nil
def cons' (A : Type) : A → list' A → list' A := list'.cons

-- Option type  
inductive option' (A : Type) : Type
| None : option' A
| Some : A → option' A

-- ==================== NatList (LF.Lists) ====================

inductive Original_LF__DOT__Lists_LF_Lists_NatList_natlist : Type
| nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist
| cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist

def Original_LF__DOT__Lists_LF_Lists_NatList_nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil

def Original_LF__DOT__Lists_LF_Lists_NatList_cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons

-- ==================== Basics (bool, negb, andb, even, eqb) ====================

inductive Original_LF__DOT__Basics_LF_Basics_bool : Type
| Original_LF__DOT__Basics_LF_Basics_bool_true : Original_LF__DOT__Basics_LF_Basics_bool
| Original_LF__DOT__Basics_LF_Basics_bool_false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.Original_LF__DOT__Basics_LF_Basics_bool_true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.Original_LF__DOT__Basics_LF_Basics_bool_false

def Original_LF__DOT__Basics_LF_Basics_negb (b : Original_LF__DOT__Basics_LF_Basics_bool) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match b with
  | .Original_LF__DOT__Basics_LF_Basics_bool_true => .Original_LF__DOT__Basics_LF_Basics_bool_false
  | .Original_LF__DOT__Basics_LF_Basics_bool_false => .Original_LF__DOT__Basics_LF_Basics_bool_true

def Original_LF__DOT__Basics_LF_Basics_andb (b1 b2 : Original_LF__DOT__Basics_LF_Basics_bool) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match b1 with
  | .Original_LF__DOT__Basics_LF_Basics_bool_true => b2
  | .Original_LF__DOT__Basics_LF_Basics_bool_false => .Original_LF__DOT__Basics_LF_Basics_bool_false

def Original_LF__DOT__Basics_LF_Basics_even : nat → Original_LF__DOT__Basics_LF_Basics_bool
| nat.O => .Original_LF__DOT__Basics_LF_Basics_bool_true
| nat.S nat.O => .Original_LF__DOT__Basics_LF_Basics_bool_false
| nat.S (nat.S n') => Original_LF__DOT__Basics_LF_Basics_even n'

def Original_LF__DOT__Basics_LF_Basics_eqb : nat → nat → Original_LF__DOT__Basics_LF_Basics_bool
| nat.O, nat.O => Original_LF__DOT__Basics_LF_Basics_true
| nat.O, nat.S _ => Original_LF__DOT__Basics_LF_Basics_false
| nat.S _, nat.O => Original_LF__DOT__Basics_LF_Basics_false
| nat.S n', nat.S m' => Original_LF__DOT__Basics_LF_Basics_eqb n' m'

-- ==================== Ascii and String ====================

inductive Ascii_ascii : Type
| Ascii : mybool → mybool → mybool → mybool → mybool → mybool → mybool → mybool → Ascii_ascii

inductive String_string : Type
| EmptyString : String_string
| String : Ascii_ascii → String_string → String_string

-- ==================== relation (LF.Rel) ====================

def Original_LF_Rel_relation (X : Type) : Type := X → X → Prop

-- ==================== Regular expressions (LF.IndProp) ====================

inductive Original_LF__DOT__IndProp_LF_IndProp_reg__exp (T : Type) : Type
| EmptySet : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
| EmptyStr : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
| Char : T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
| App : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
| Union : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
| Star : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T

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

-- ==================== Maps (LF.Maps) ====================

def Original_LF__DOT__Maps_LF_Maps_total__map (A : Type) : Type := String_string → A

def Original_LF__DOT__Maps_LF_Maps_t__empty {A : Type} (v : A) : Original_LF__DOT__Maps_LF_Maps_total__map A :=
  fun _ => v

-- String equality functions
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

def Original_LF__DOT__Maps_LF_Maps_t__update {A : Type} (m : Original_LF__DOT__Maps_LF_Maps_total__map A)
    (x : String_string) (v : A) : Original_LF__DOT__Maps_LF_Maps_total__map A :=
  fun x' => match String_eqb x x' with
            | mybool.mytrue => v
            | mybool.myfalse => m x'

-- ==================== Imp language (LF.Imp) ====================

def Original_LF__DOT__Imp_LF_Imp_state : Type := Original_LF__DOT__Maps_LF_Maps_total__map nat

-- X variable definition
def Original_LF__DOT__Imp_LF_Imp_X : String_string :=
  String_string.String
    (Ascii_ascii.Ascii mybool.myfalse mybool.myfalse mybool.myfalse mybool.mytrue
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

-- Bool negation/conjunction for beval
def negb : mybool → mybool
| mybool.mytrue => mybool.myfalse
| mybool.myfalse => mybool.mytrue

def andb : mybool → mybool → mybool
| mybool.mytrue, b2 => b2
| mybool.myfalse, _ => mybool.myfalse

-- Nat comparison for aeval/beval
def nat_eqb : nat → nat → mybool
| nat.O, nat.O => mybool.mytrue
| nat.O, nat.S _ => mybool.myfalse
| nat.S _, nat.O => mybool.myfalse
| nat.S n', nat.S m' => nat_eqb n' m'

def nat_leb : nat → nat → mybool
| nat.O, _ => mybool.mytrue
| nat.S _, nat.O => mybool.myfalse
| nat.S n', nat.S m' => nat_leb n' m'

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
    nat_sub (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
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

-- ==================== Logic.In (LF.Logic) ====================

def Original_LF__DOT__Logic_LF_Logic_In {A : Type} (a : A) : Original_LF__DOT__Poly_LF_Poly_list A → Prop
| Original_LF__DOT__Poly_LF_Poly_list.nil => False'
| Original_LF__DOT__Poly_LF_Poly_list.cons b l => or' (Corelib_Init_Logic_eq b a) (Original_LF__DOT__Logic_LF_Logic_In a l)

-- List.In for standard list
def List_In {A : Type} (a : A) : list' A → Prop
| list'.nil => False'
| list'.cons b l => or' (Corelib_Init_Logic_eq b a) (List_In a l)
