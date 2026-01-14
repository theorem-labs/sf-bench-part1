-- Comprehensive Lean translation for loop_never_stops and all dependencies
set_option linter.all false

-- ============================================================================
-- Basic Types
-- ============================================================================

-- Define our own bool type  
inductive mybool : Type where
  | mytrue : mybool
  | myfalse : mybool

def mybool2 := mybool
def mytrue := mybool.mytrue
def myfalse := mybool.myfalse

-- Define our own nat type
inductive nat : Type where
  | O : nat
  | S : nat → nat

def nat_O := nat.O
def nat_S := nat.S
def _0 : nat := nat.O
def S : nat → nat := nat.S

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

def bool_eqb : mybool → mybool → mybool
  | mybool.mytrue, mybool.mytrue => mybool.mytrue
  | mybool.myfalse, mybool.myfalse => mybool.mytrue
  | _, _ => mybool.myfalse

-- ============================================================================
-- ASCII and String Types
-- ============================================================================

inductive Ascii_ascii : Type where
  | Ascii : mybool → mybool → mybool → mybool → mybool → mybool → mybool → mybool → Ascii_ascii

def Ascii_Ascii := Ascii_ascii.Ascii

def Ascii_eqb : Ascii_ascii → Ascii_ascii → mybool
  | Ascii_ascii.Ascii a0 a1 a2 a3 a4 a5 a6 a7, Ascii_ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    bool_andb (bool_eqb a0 b0) (bool_andb (bool_eqb a1 b1) (bool_andb (bool_eqb a2 b2) 
      (bool_andb (bool_eqb a3 b3) (bool_andb (bool_eqb a4 b4) (bool_andb (bool_eqb a5 b5) 
        (bool_andb (bool_eqb a6 b6) (bool_eqb a7 b7)))))))

inductive String_string : Type where
  | EmptyString : String_string
  | String : Ascii_ascii → String_string → String_string

def String_EmptyString := String_string.EmptyString
def String_String := String_string.String

def String_eqb : String_string → String_string → mybool
  | String_string.EmptyString, String_string.EmptyString => mybool.mytrue
  | String_string.String c1 s1, String_string.String c2 s2 => 
      bool_andb (Ascii_eqb c1 c2) (String_eqb s1 s2)
  | _, _ => mybool.myfalse

-- ============================================================================
-- Maps
-- ============================================================================

def Original_LF__DOT__Maps_LF_Maps_total__map (A : Type) := String_string → A

def Original_LF__DOT__Maps_LF_Maps_t__empty {A : Type} (v : A) : Original_LF__DOT__Maps_LF_Maps_total__map A :=
  fun _ => v

def Original_LF__DOT__Maps_LF_Maps_t__update {A : Type} (m : Original_LF__DOT__Maps_LF_Maps_total__map A)
    (x : String_string) (v : A) : Original_LF__DOT__Maps_LF_Maps_total__map A :=
  fun x' => match String_eqb x x' with
    | mybool.mytrue => v
    | mybool.myfalse => m x'

-- ============================================================================
-- Imp Language
-- ============================================================================

def Original_LF__DOT__Imp_LF_Imp_state := Original_LF__DOT__Maps_LF_Maps_total__map nat

-- Arithmetic expressions
inductive Original_LF__DOT__Imp_LF_Imp_aexp : Type where
  | ANum : nat → Original_LF__DOT__Imp_LF_Imp_aexp
  | AId : String_string → Original_LF__DOT__Imp_LF_Imp_aexp
  | APlus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp
  | AMinus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp
  | AMult : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp

def Original_LF__DOT__Imp_LF_Imp_ANum := Original_LF__DOT__Imp_LF_Imp_aexp.ANum
def Original_LF__DOT__Imp_LF_Imp_AId := Original_LF__DOT__Imp_LF_Imp_aexp.AId
def Original_LF__DOT__Imp_LF_Imp_APlus := Original_LF__DOT__Imp_LF_Imp_aexp.APlus
def Original_LF__DOT__Imp_LF_Imp_AMinus := Original_LF__DOT__Imp_LF_Imp_aexp.AMinus
def Original_LF__DOT__Imp_LF_Imp_AMult := Original_LF__DOT__Imp_LF_Imp_aexp.AMult

-- Boolean expressions
inductive Original_LF__DOT__Imp_LF_Imp_bexp : Type where
  | BTrue : Original_LF__DOT__Imp_LF_Imp_bexp
  | BFalse : Original_LF__DOT__Imp_LF_Imp_bexp
  | BEq : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BNeq : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BLe : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BGt : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BNot : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BAnd : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp

def Original_LF__DOT__Imp_LF_Imp_BTrue := Original_LF__DOT__Imp_LF_Imp_bexp.BTrue
def Original_LF__DOT__Imp_LF_Imp_BFalse := Original_LF__DOT__Imp_LF_Imp_bexp.BFalse
def Original_LF__DOT__Imp_LF_Imp_BEq := Original_LF__DOT__Imp_LF_Imp_bexp.BEq
def Original_LF__DOT__Imp_LF_Imp_BNeq := Original_LF__DOT__Imp_LF_Imp_bexp.BNeq
def Original_LF__DOT__Imp_LF_Imp_BLe := Original_LF__DOT__Imp_LF_Imp_bexp.BLe
def Original_LF__DOT__Imp_LF_Imp_BGt := Original_LF__DOT__Imp_LF_Imp_bexp.BGt
def Original_LF__DOT__Imp_LF_Imp_BNot := Original_LF__DOT__Imp_LF_Imp_bexp.BNot
def Original_LF__DOT__Imp_LF_Imp_BAnd := Original_LF__DOT__Imp_LF_Imp_bexp.BAnd
-- Aliases with bexp_ prefix for isomorphism files
def Original_LF__DOT__Imp_LF_Imp_bexp_BTrue := Original_LF__DOT__Imp_LF_Imp_bexp.BTrue
-- Alias without bexp_ prefix (needed by U2_btrue__iso)
-- Note: this is the same as Original_LF__DOT__Imp_LF_Imp_BTrue already defined above

-- Commands
inductive Original_LF__DOT__Imp_LF_Imp_com : Type where
  | CSkip : Original_LF__DOT__Imp_LF_Imp_com
  | CAsgn : String_string → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_com
  | CSeq : Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com
  | CIf : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com
  | CWhile : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com

-- Explicit definitions for command constructors (needed for checker)
def Original_LF__DOT__Imp_LF_Imp_CSkip : Original_LF__DOT__Imp_LF_Imp_com := Original_LF__DOT__Imp_LF_Imp_com.CSkip
def Original_LF__DOT__Imp_LF_Imp_CAsgn : String_string → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_com := Original_LF__DOT__Imp_LF_Imp_com.CAsgn
def Original_LF__DOT__Imp_LF_Imp_CSeq : Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com := Original_LF__DOT__Imp_LF_Imp_com.CSeq
def Original_LF__DOT__Imp_LF_Imp_CIf : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com := Original_LF__DOT__Imp_LF_Imp_com.CIf
def Original_LF__DOT__Imp_LF_Imp_CWhile : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com := Original_LF__DOT__Imp_LF_Imp_com.CWhile
-- Aliases with com_ prefix for isomorphism files
def Original_LF__DOT__Imp_LF_Imp_com_CSkip := Original_LF__DOT__Imp_LF_Imp_com.CSkip
def Original_LF__DOT__Imp_LF_Imp_com_CAsgn := Original_LF__DOT__Imp_LF_Imp_com.CAsgn
def Original_LF__DOT__Imp_LF_Imp_com_CSeq := Original_LF__DOT__Imp_LF_Imp_com.CSeq
def Original_LF__DOT__Imp_LF_Imp_com_CIf := Original_LF__DOT__Imp_LF_Imp_com.CIf
def Original_LF__DOT__Imp_LF_Imp_com_CWhile := Original_LF__DOT__Imp_LF_Imp_com.CWhile

-- Evaluation functions
def Original_LF__DOT__Imp_LF_Imp_aeval (st : Original_LF__DOT__Imp_LF_Imp_state) : Original_LF__DOT__Imp_LF_Imp_aexp → nat
  | Original_LF__DOT__Imp_LF_Imp_aexp.ANum n => n
  | Original_LF__DOT__Imp_LF_Imp_aexp.AId x => st x
  | Original_LF__DOT__Imp_LF_Imp_aexp.APlus a1 a2 => nat_add (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
  | Original_LF__DOT__Imp_LF_Imp_aexp.AMinus a1 a2 => nat_sub (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
  | Original_LF__DOT__Imp_LF_Imp_aexp.AMult a1 a2 => nat_mul (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)

def Original_LF__DOT__Imp_LF_Imp_beval (st : Original_LF__DOT__Imp_LF_Imp_state) : Original_LF__DOT__Imp_LF_Imp_bexp → mybool
  | Original_LF__DOT__Imp_LF_Imp_bexp.BTrue => mybool.mytrue
  | Original_LF__DOT__Imp_LF_Imp_bexp.BFalse => mybool.myfalse
  | Original_LF__DOT__Imp_LF_Imp_bexp.BEq a1 a2 => nat_eqb (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
  | Original_LF__DOT__Imp_LF_Imp_bexp.BNeq a1 a2 => bool_negb (nat_eqb (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2))
  | Original_LF__DOT__Imp_LF_Imp_bexp.BLe a1 a2 => nat_leb (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
  | Original_LF__DOT__Imp_LF_Imp_bexp.BGt a1 a2 => bool_negb (nat_leb (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2))
  | Original_LF__DOT__Imp_LF_Imp_bexp.BNot b => bool_negb (Original_LF__DOT__Imp_LF_Imp_beval st b)
  | Original_LF__DOT__Imp_LF_Imp_bexp.BAnd b1 b2 => bool_andb (Original_LF__DOT__Imp_LF_Imp_beval st b1) (Original_LF__DOT__Imp_LF_Imp_beval st b2)

-- ============================================================================
-- Logic Types  
-- ============================================================================

-- False type (empty proposition)
inductive MyFalse : Prop where

-- True type
inductive MyTrue : Prop where
  | I : MyTrue

def MyTrue_I : MyTrue := MyTrue.I

-- Logic.not definition
def Logic_not (P : Prop) : Prop := P → MyFalse

-- Equality type for Type
inductive Corelib_Init_Logic_eq {A : Type} (a : A) : A → Prop
| refl : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a := 
  Corelib_Init_Logic_eq.refl

-- Equality type for Prop
inductive Corelib_Init_Logic_eq_Prop {A : Prop} (a : A) : A → Prop
| refl : Corelib_Init_Logic_eq_Prop a a

def Corelib_Init_Logic_eq_Prop_refl {A : Prop} (a : A) : Corelib_Init_Logic_eq_Prop a a := 
  Corelib_Init_Logic_eq_Prop.refl

-- ============================================================================
-- List type
-- ============================================================================

inductive list (A : Type) : Type where
  | nil : list A
  | cons : A → list A → list A

def nil {A : Type} : list A := list.nil
def cons {A : Type} : A → list A → list A := list.cons

def app {A : Type} (l1 l2 : list A) : list A :=
  match l1 with
  | list.nil => l2
  | list.cons h t => list.cons h (app t l2)

-- ============================================================================
-- ceval - Command Evaluation Relation
-- ============================================================================

inductive Original_LF__DOT__Imp_LF_Imp_ceval : Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_state → Original_LF__DOT__Imp_LF_Imp_state → Prop where
  | E_Skip : ∀ (st : Original_LF__DOT__Imp_LF_Imp_state),
      Original_LF__DOT__Imp_LF_Imp_ceval Original_LF__DOT__Imp_LF_Imp_com.CSkip st st
  | E_Asgn : ∀ (st : Original_LF__DOT__Imp_LF_Imp_state) (a : Original_LF__DOT__Imp_LF_Imp_aexp) (n : nat) (x : String_string),
      Corelib_Init_Logic_eq (Original_LF__DOT__Imp_LF_Imp_aeval st a) n →
      Original_LF__DOT__Imp_LF_Imp_ceval (Original_LF__DOT__Imp_LF_Imp_com.CAsgn x a) st (Original_LF__DOT__Maps_LF_Maps_t__update st x n)
  | E_Seq : ∀ (c1 c2 : Original_LF__DOT__Imp_LF_Imp_com) (st st' st'' : Original_LF__DOT__Imp_LF_Imp_state),
      Original_LF__DOT__Imp_LF_Imp_ceval c1 st st' →
      Original_LF__DOT__Imp_LF_Imp_ceval c2 st' st'' →
      Original_LF__DOT__Imp_LF_Imp_ceval (Original_LF__DOT__Imp_LF_Imp_com.CSeq c1 c2) st st''
  | E_IfTrue : ∀ (st st' : Original_LF__DOT__Imp_LF_Imp_state) (b : Original_LF__DOT__Imp_LF_Imp_bexp) (c1 c2 : Original_LF__DOT__Imp_LF_Imp_com),
      Corelib_Init_Logic_eq (Original_LF__DOT__Imp_LF_Imp_beval st b) mybool.mytrue →
      Original_LF__DOT__Imp_LF_Imp_ceval c1 st st' →
      Original_LF__DOT__Imp_LF_Imp_ceval (Original_LF__DOT__Imp_LF_Imp_com.CIf b c1 c2) st st'
  | E_IfFalse : ∀ (st st' : Original_LF__DOT__Imp_LF_Imp_state) (b : Original_LF__DOT__Imp_LF_Imp_bexp) (c1 c2 : Original_LF__DOT__Imp_LF_Imp_com),
      Corelib_Init_Logic_eq (Original_LF__DOT__Imp_LF_Imp_beval st b) mybool.myfalse →
      Original_LF__DOT__Imp_LF_Imp_ceval c2 st st' →
      Original_LF__DOT__Imp_LF_Imp_ceval (Original_LF__DOT__Imp_LF_Imp_com.CIf b c1 c2) st st'
  | E_WhileFalse : ∀ (b : Original_LF__DOT__Imp_LF_Imp_bexp) (st : Original_LF__DOT__Imp_LF_Imp_state) (c : Original_LF__DOT__Imp_LF_Imp_com),
      Corelib_Init_Logic_eq (Original_LF__DOT__Imp_LF_Imp_beval st b) mybool.myfalse →
      Original_LF__DOT__Imp_LF_Imp_ceval (Original_LF__DOT__Imp_LF_Imp_com.CWhile b c) st st
  | E_WhileTrue : ∀ (st st' st'' : Original_LF__DOT__Imp_LF_Imp_state) (b : Original_LF__DOT__Imp_LF_Imp_bexp) (c : Original_LF__DOT__Imp_LF_Imp_com),
      Corelib_Init_Logic_eq (Original_LF__DOT__Imp_LF_Imp_beval st b) mybool.mytrue →
      Original_LF__DOT__Imp_LF_Imp_ceval c st st' →
      Original_LF__DOT__Imp_LF_Imp_ceval (Original_LF__DOT__Imp_LF_Imp_com.CWhile b c) st' st'' →
      Original_LF__DOT__Imp_LF_Imp_ceval (Original_LF__DOT__Imp_LF_Imp_com.CWhile b c) st st''

-- ============================================================================
-- loop definition: while true do skip end
-- ============================================================================

def Original_LF__DOT__Imp_LF_Imp_loop : Original_LF__DOT__Imp_LF_Imp_com :=
  Original_LF__DOT__Imp_LF_Imp_com.CWhile Original_LF__DOT__Imp_LF_Imp_bexp.BTrue Original_LF__DOT__Imp_LF_Imp_com.CSkip

-- ============================================================================
-- loop_never_stops theorem (Admitted in Original, so we use axiom)
-- ============================================================================

axiom Original_LF__DOT__Imp_LF_Imp_loop__never__stops : 
  ∀ (st st' : Original_LF__DOT__Imp_LF_Imp_state),
    Original_LF__DOT__Imp_LF_Imp_ceval Original_LF__DOT__Imp_LF_Imp_loop st st' → MyFalse
