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

-- Aliases for bool
def mybool2 := mybool
def bool_true := mybool.mytrue
def bool_false := mybool.myfalse
def mybool_mytrue := mybool.mytrue
def mybool_myfalse := mybool.myfalse
def mybool_alias := mybool
def true := mybool.mytrue
def false := mybool.myfalse

-- Define our own nat type
inductive nat : Type where
  | O : nat
  | S : nat → nat

-- Aliases that will become Imported.nat, etc.
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

def nat_pred : nat → nat
  | nat.O => nat.O
  | nat.S n => n

def Nat_add := nat_add
def Nat_sub := nat_sub
def Nat_mul := nat_mul
def Nat_pred := nat_pred

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
-- Basics types (LF.Basics.bool, etc.)
-- ============================================================================

-- Boolean type (matching LF.Basics.bool)
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- eqb function (equality test for nat) for Basics
def Original_LF__DOT__Basics_LF_Basics_eqb : nat → nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.true
  | nat.O, nat.S _ => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S _, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S n', nat.S m' => Original_LF__DOT__Basics_LF_Basics_eqb n' m'

-- plus, mult, exp from Basics
def Original_LF__DOT__Basics_LF_Basics_plus : nat → nat → nat
  | nat.O, m => m
  | nat.S n', m => nat.S (Original_LF__DOT__Basics_LF_Basics_plus n' m)

def Original_LF__DOT__Basics_LF_Basics_mult : nat → nat → nat
  | nat.O, _ => nat.O
  | nat.S n', m => Original_LF__DOT__Basics_LF_Basics_plus m (Original_LF__DOT__Basics_LF_Basics_mult n' m)

def Original_LF__DOT__Basics_LF_Basics_exp : nat → nat → nat
  | base, nat.O => nat.S nat.O  -- base^0 = 1
  | base, nat.S p => Original_LF__DOT__Basics_LF_Basics_mult base (Original_LF__DOT__Basics_LF_Basics_exp base p)

-- ============================================================================
-- Option, Prod, List
-- ============================================================================

inductive option (A : Type) : Type where
  | None : option A
  | Some : A → option A

def None (A : Type) : option A := option.None
def Some (A : Type) (a : A) : option A := option.Some a

inductive prod (A B : Type) : Type where
  | pair : A → B → prod A B

def pair (A B : Type) (a : A) (b : B) : prod A B := prod.pair a b

inductive list (A : Type) : Type where
  | nil : list A
  | cons : A → list A → list A

def nil (A : Type) : list A := list.nil
def list_nil (A : Type) : list A := list.nil
def cons (A : Type) (h : A) (t : list A) : list A := list.cons h t
def list_cons (A : Type) (h : A) (t : list A) : list A := list.cons h t

def app (A : Type) : list A → list A → list A
  | list.nil, l2 => l2
  | list.cons h t, l2 => list.cons h (app A t l2)

-- ============================================================================
-- Prop types and Logic
-- ============================================================================

inductive TrueType : Prop where
  | I : TrueType

def TrueType_I := TrueType.I

inductive FalseType : Prop where

-- Logical or
inductive or (A B : Prop) : Prop where
  | inl : A → or A B
  | inr : B → or A B

def Logic_not (P : Prop) : Prop := P → FalseType

-- Equality type in Prop (will become SProp in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} (a : A) : A → Prop where
  | refl : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl

-- Equality for Prop-level elements
inductive Corelib_Init_Logic_eq_Prop {A : Prop} (a : A) : A → Prop where
  | refl : Corelib_Init_Logic_eq_Prop a a

-- List_In
def List_In (A : Type) (a : A) : list A → Prop
  | list.nil => FalseType
  | list.cons x xs => or (Corelib_Init_Logic_eq x a) (List_In A a xs)

-- existential
inductive ex {A : Type} (P : A → Prop) : Prop where
  | intro : ∀ x, P x → ex P

def ex_intro {A : Type} (P : A → Prop) (x : A) (h : P x) : ex P := ex.intro x h

-- iff
inductive iff (A B : Prop) : Prop where
  | intro : A → B → iff A B

def iff_intro (A B : Prop) (h1 : A) (h2 : B) : iff A B := iff.intro h1 h2

-- ============================================================================
-- Ascii and String
-- ============================================================================

inductive Ascii_ascii : Type where
  | Ascii : mybool → mybool → mybool → mybool → mybool → mybool → mybool → mybool → Ascii_ascii

def Ascii := Ascii_ascii
def Ascii_Ascii := Ascii_ascii.Ascii

def Ascii_eqb : Ascii_ascii → Ascii_ascii → mybool
  | Ascii_ascii.Ascii a1 a2 a3 a4 a5 a6 a7 a8, Ascii_ascii.Ascii b1 b2 b3 b4 b5 b6 b7 b8 =>
    bool_andb (bool_eqb a1 b1) (bool_andb (bool_eqb a2 b2) (bool_andb (bool_eqb a3 b3) (bool_andb (bool_eqb a4 b4) (bool_andb (bool_eqb a5 b5) (bool_andb (bool_eqb a6 b6) (bool_andb (bool_eqb a7 b7) (bool_eqb a8 b8)))))))

inductive String_string : Type where
  | EmptyString : String_string
  | String : Ascii_ascii → String_string → String_string

def String_EmptyString := String_string.EmptyString
def String_String := String_string.String

def String_eqb : String_string → String_string → mybool
  | String_string.EmptyString, String_string.EmptyString => mybool.mytrue
  | String_string.String c1 s1, String_string.String c2 s2 => bool_andb (Ascii_eqb c1 c2) (String_eqb s1 s2)
  | _, _ => mybool.myfalse

-- X, Y, Z character definitions (specific ASCII values)
-- X = ASCII 88 = 0b01011000
def char_X : Ascii_ascii := Ascii_ascii.Ascii mybool.myfalse mybool.myfalse mybool.myfalse mybool.mytrue mybool.mytrue mybool.myfalse mybool.mytrue mybool.myfalse
-- Y = ASCII 89 = 0b01011001
def char_Y : Ascii_ascii := Ascii_ascii.Ascii mybool.mytrue mybool.myfalse mybool.myfalse mybool.mytrue mybool.mytrue mybool.myfalse mybool.mytrue mybool.myfalse
-- Z = ASCII 90 = 0b01011010
def char_Z : Ascii_ascii := Ascii_ascii.Ascii mybool.myfalse mybool.mytrue mybool.myfalse mybool.mytrue mybool.mytrue mybool.myfalse mybool.mytrue mybool.myfalse

-- ============================================================================
-- Maps module
-- ============================================================================

def Original_LF__DOT__Maps_LF_Maps_total__map (A : Type) := String_string → A
def Original_LF__DOT__Maps_LF_Maps_t__empty (A : Type) (v : A) : Original_LF__DOT__Maps_LF_Maps_total__map A :=
  fun _ => v

def Original_LF__DOT__Maps_LF_Maps_t__update (A : Type) (m : Original_LF__DOT__Maps_LF_Maps_total__map A) (x : String_string) (v : A) : Original_LF__DOT__Maps_LF_Maps_total__map A :=
  fun y => match String_eqb x y with
    | mybool.mytrue => v
    | mybool.myfalse => m y

-- ============================================================================
-- Imp module - state, expressions, commands
-- ============================================================================

def Original_LF__DOT__Imp_LF_Imp_state := Original_LF__DOT__Maps_LF_Maps_total__map nat
def Original_LF__DOT__Imp_LF_Imp_X : String_string := String_string.String char_X String_string.EmptyString
def Original_LF__DOT__Imp_LF_Imp_Y : String_string := String_string.String char_Y String_string.EmptyString
def Original_LF__DOT__Imp_LF_Imp_Z : String_string := String_string.String char_Z String_string.EmptyString
def Original_LF__DOT__Imp_LF_Imp_empty__st : Original_LF__DOT__Imp_LF_Imp_state := Original_LF__DOT__Maps_LF_Maps_t__empty nat nat.O

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

-- Commands
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
  | Original_LF__DOT__Imp_LF_Imp_bexp.BNot b => bool_negb (Original_LF__DOT__Imp_LF_Imp_beval st b)
  | Original_LF__DOT__Imp_LF_Imp_bexp.BAnd b1 b2 => bool_andb (Original_LF__DOT__Imp_LF_Imp_beval st b1) (Original_LF__DOT__Imp_LF_Imp_beval st b2)

-- ceval: big-step semantics for commands
inductive Original_LF__DOT__Imp_LF_Imp_ceval : Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_state → Original_LF__DOT__Imp_LF_Imp_state → Prop where
  | E_Skip : ∀ st, Original_LF__DOT__Imp_LF_Imp_ceval Original_LF__DOT__Imp_LF_Imp_com.CSkip st st
  | E_Asgn : ∀ st x a, Original_LF__DOT__Imp_LF_Imp_ceval (Original_LF__DOT__Imp_LF_Imp_com.CAsgn x a) st (Original_LF__DOT__Maps_LF_Maps_t__update nat st x (Original_LF__DOT__Imp_LF_Imp_aeval st a))
  | E_Seq : ∀ c1 c2 st st' st'', Original_LF__DOT__Imp_LF_Imp_ceval c1 st st' → Original_LF__DOT__Imp_LF_Imp_ceval c2 st' st'' → Original_LF__DOT__Imp_LF_Imp_ceval (Original_LF__DOT__Imp_LF_Imp_com.CSeq c1 c2) st st''
  | E_IfTrue : ∀ st st' b c1 c2, Original_LF__DOT__Imp_LF_Imp_beval st b = mybool.mytrue → Original_LF__DOT__Imp_LF_Imp_ceval c1 st st' → Original_LF__DOT__Imp_LF_Imp_ceval (Original_LF__DOT__Imp_LF_Imp_com.CIf b c1 c2) st st'
  | E_IfFalse : ∀ st st' b c1 c2, Original_LF__DOT__Imp_LF_Imp_beval st b = mybool.myfalse → Original_LF__DOT__Imp_LF_Imp_ceval c2 st st' → Original_LF__DOT__Imp_LF_Imp_ceval (Original_LF__DOT__Imp_LF_Imp_com.CIf b c1 c2) st st'
  | E_WhileFalse : ∀ b st c, Original_LF__DOT__Imp_LF_Imp_beval st b = mybool.myfalse → Original_LF__DOT__Imp_LF_Imp_ceval (Original_LF__DOT__Imp_LF_Imp_com.CWhile b c) st st
  | E_WhileTrue : ∀ st st' st'' b c, Original_LF__DOT__Imp_LF_Imp_beval st b = mybool.mytrue → Original_LF__DOT__Imp_LF_Imp_ceval c st st' → Original_LF__DOT__Imp_LF_Imp_ceval (Original_LF__DOT__Imp_LF_Imp_com.CWhile b c) st' st'' → Original_LF__DOT__Imp_LF_Imp_ceval (Original_LF__DOT__Imp_LF_Imp_com.CWhile b c) st st''

def Original_LF__DOT__Imp_LF_Imp_ceval_E__Skip := @Original_LF__DOT__Imp_LF_Imp_ceval.E_Skip
def Original_LF__DOT__Imp_LF_Imp_ceval_E__Asgn := @Original_LF__DOT__Imp_LF_Imp_ceval.E_Asgn
def Original_LF__DOT__Imp_LF_Imp_ceval_E__Seq := @Original_LF__DOT__Imp_LF_Imp_ceval.E_Seq
def Original_LF__DOT__Imp_LF_Imp_ceval_E__IfTrue := @Original_LF__DOT__Imp_LF_Imp_ceval.E_IfTrue
def Original_LF__DOT__Imp_LF_Imp_ceval_E__IfFalse := @Original_LF__DOT__Imp_LF_Imp_ceval.E_IfFalse
def Original_LF__DOT__Imp_LF_Imp_ceval_E__WhileFalse := @Original_LF__DOT__Imp_LF_Imp_ceval.E_WhileFalse
def Original_LF__DOT__Imp_LF_Imp_ceval_E__WhileTrue := @Original_LF__DOT__Imp_LF_Imp_ceval.E_WhileTrue

-- ceval_example2: empty_st =[ X := 0; Y := 1; Z := 2 ]=> (Z !-> 2 ; Y !-> 1 ; X !-> 0)
axiom Original_LF__DOT__Imp_LF_Imp_ceval__example2 :
  Original_LF__DOT__Imp_LF_Imp_ceval
    (.CSeq
      (.CAsgn Original_LF__DOT__Imp_LF_Imp_X (.ANum nat.O))
      (.CSeq
        (.CAsgn Original_LF__DOT__Imp_LF_Imp_Y (.ANum (nat.S nat.O)))
        (.CAsgn Original_LF__DOT__Imp_LF_Imp_Z (.ANum (nat.S (nat.S nat.O))))))
    Original_LF__DOT__Imp_LF_Imp_empty__st
    (Original_LF__DOT__Maps_LF_Maps_t__update nat
      (Original_LF__DOT__Maps_LF_Maps_t__update nat
        (Original_LF__DOT__Maps_LF_Maps_t__update nat Original_LF__DOT__Imp_LF_Imp_empty__st Original_LF__DOT__Imp_LF_Imp_X nat.O)
        Original_LF__DOT__Imp_LF_Imp_Y (nat.S nat.O))
      Original_LF__DOT__Imp_LF_Imp_Z (nat.S (nat.S nat.O)))

-- ============================================================================
-- Stack machine instructions (sinstr)
-- ============================================================================

inductive Original_LF__DOT__Imp_LF_Imp_sinstr : Type where
  | SPush : nat → Original_LF__DOT__Imp_LF_Imp_sinstr
  | SLoad : String_string → Original_LF__DOT__Imp_LF_Imp_sinstr
  | SPlus : Original_LF__DOT__Imp_LF_Imp_sinstr
  | SMinus : Original_LF__DOT__Imp_LF_Imp_sinstr
  | SMult : Original_LF__DOT__Imp_LF_Imp_sinstr

def Original_LF__DOT__Imp_LF_Imp_sinstr_SPush := Original_LF__DOT__Imp_LF_Imp_sinstr.SPush
def Original_LF__DOT__Imp_LF_Imp_sinstr_SLoad := Original_LF__DOT__Imp_LF_Imp_sinstr.SLoad
def Original_LF__DOT__Imp_LF_Imp_sinstr_SPlus := Original_LF__DOT__Imp_LF_Imp_sinstr.SPlus
def Original_LF__DOT__Imp_LF_Imp_sinstr_SMinus := Original_LF__DOT__Imp_LF_Imp_sinstr.SMinus
def Original_LF__DOT__Imp_LF_Imp_sinstr_SMult := Original_LF__DOT__Imp_LF_Imp_sinstr.SMult

-- s_compile and s_execute are Admitted in Original.v
axiom Original_LF__DOT__Imp_LF_Imp_s__compile : Original_LF__DOT__Imp_LF_Imp_aexp → list Original_LF__DOT__Imp_LF_Imp_sinstr

axiom Original_LF__DOT__Imp_LF_Imp_s__execute : 
  Original_LF__DOT__Imp_LF_Imp_state → list nat → list Original_LF__DOT__Imp_LF_Imp_sinstr → list nat

-- s_compile_correct: Admitted in Original.v
axiom Original_LF__DOT__Imp_LF_Imp_s__compile__correct :
  ∀ (st : Original_LF__DOT__Imp_LF_Imp_state) (e : Original_LF__DOT__Imp_LF_Imp_aexp),
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__Imp_LF_Imp_s__execute st (list.nil) (Original_LF__DOT__Imp_LF_Imp_s__compile e))
    (list.cons (Original_LF__DOT__Imp_LF_Imp_aeval st e) list.nil)

-- ============================================================================
-- Lists module - natlist, partial_map, etc.
-- ============================================================================

-- natlist (list of nats)
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natlist : Type where
  | nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist

def Original_LF__DOT__Lists_LF_Lists_NatList_nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil

def Original_LF__DOT__Lists_LF_Lists_NatList_cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons

-- app function for natlist
def Original_LF__DOT__Lists_LF_Lists_NatList_app : Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil, l2 => l2
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h t, l2 => 
      Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h (Original_LF__DOT__Lists_LF_Lists_NatList_app t l2)

-- natoption
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natoption : Type where
  | None : Original_LF__DOT__Lists_LF_Lists_NatList_natoption
  | Some : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natoption

def Original_LF__DOT__Lists_LF_Lists_NatList_None : Original_LF__DOT__Lists_LF_Lists_NatList_natoption :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natoption.None

def Original_LF__DOT__Lists_LF_Lists_NatList_Some : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natoption :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natoption.Some

-- hd function  
def Original_LF__DOT__Lists_LF_Lists_NatList_hd (default : nat) (l : Original_LF__DOT__Lists_LF_Lists_NatList_natlist) : nat :=
  match l with
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil => default
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h _ => h

-- option_elim function
def Original_LF__DOT__Lists_LF_Lists_NatList_option__elim (d : nat) (o : Original_LF__DOT__Lists_LF_Lists_NatList_natoption) : nat :=
  match o with
  | Original_LF__DOT__Lists_LF_Lists_NatList_natoption.Some n' => n'
  | Original_LF__DOT__Lists_LF_Lists_NatList_natoption.None => d

-- hd_error function (Admitted in Original.v)
axiom Original_LF__DOT__Lists_LF_Lists_NatList_hd__error :
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natoption

-- option_elim_hd theorem (Admitted in Original.v)
axiom Original_LF__DOT__Lists_LF_Lists_NatList_option__elim__hd :
  ∀ (l : Original_LF__DOT__Lists_LF_Lists_NatList_natlist) (default : nat),
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__Lists_LF_Lists_NatList_hd default l)
    (Original_LF__DOT__Lists_LF_Lists_NatList_option__elim default (Original_LF__DOT__Lists_LF_Lists_NatList_hd__error l))

-- nth_error function
def Original_LF__DOT__Lists_LF_Lists_NatList_nth__error : Original_LF__DOT__Lists_LF_Lists_NatList_natlist → nat → Original_LF__DOT__Lists_LF_Lists_NatList_natoption
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil, _ => Original_LF__DOT__Lists_LF_Lists_NatList_natoption.None
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons a l', nat.O => Original_LF__DOT__Lists_LF_Lists_NatList_natoption.Some a
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons _ l', nat.S n' => Original_LF__DOT__Lists_LF_Lists_NatList_nth__error l' n'

-- rev function
def Original_LF__DOT__Lists_LF_Lists_NatList_rev : Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil => Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h t => 
    Original_LF__DOT__Lists_LF_Lists_NatList_app (Original_LF__DOT__Lists_LF_Lists_NatList_rev t) 
      (Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil)

-- test_hd_error1 : hd_error [] = None (Admitted in Original.v)
axiom Original_LF__DOT__Lists_LF_Lists_NatList_test__hd__error1 :
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__Lists_LF_Lists_NatList_hd__error Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil)
    Original_LF__DOT__Lists_LF_Lists_NatList_natoption.None

-- test_hd_error2 : hd_error [1] = Some 1 (Admitted in Original.v)
axiom Original_LF__DOT__Lists_LF_Lists_NatList_test__hd__error2 :
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__Lists_LF_Lists_NatList_hd__error (Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons (nat.S nat.O) Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil))
    (Original_LF__DOT__Lists_LF_Lists_NatList_natoption.Some (nat.S nat.O))

-- test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7 (Admitted in Original.v)
def nat4 : nat := nat.S (nat.S (nat.S (nat.S nat.O)))
def nat5' : nat := nat.S nat4
def nat6 : nat := nat.S nat5'
def nat7 : nat := nat.S nat6

axiom Original_LF__DOT__Lists_LF_Lists_NatList_test__nth__error2 :
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__Lists_LF_Lists_NatList_nth__error 
      (Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons nat4 
        (Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons nat5' 
          (Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons nat6 
            (Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons nat7 Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil))))
      (nat.S (nat.S (nat.S nat.O))))
    (Original_LF__DOT__Lists_LF_Lists_NatList_natoption.Some nat7)

-- test_nth_error3 : nth_error [4;5;6;7] 9 = None (Admitted in Original.v)
def nat9 : nat := nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))))))

axiom Original_LF__DOT__Lists_LF_Lists_NatList_test__nth__error3 :
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__Lists_LF_Lists_NatList_nth__error 
      (Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons nat4 
        (Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons nat5' 
          (Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons nat6 
            (Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons nat7 Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil))))
      nat9)
    Original_LF__DOT__Lists_LF_Lists_NatList_natoption.None

-- test_rev1 : rev [1;2;3] = [3;2;1] (Admitted in Original.v)
def nat1 : nat := nat.S nat.O
def nat2' : nat := nat.S nat1
def nat3' : nat := nat.S nat2'

axiom Original_LF__DOT__Lists_LF_Lists_NatList_test__rev1 :
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__Lists_LF_Lists_NatList_rev 
      (Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons nat1 
        (Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons nat2' 
          (Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons nat3' Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil))))
    (Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons nat3' 
      (Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons nat2' 
        (Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons nat1 Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil)))

-- test_rev2 : rev nil = nil (Admitted in Original.v)
axiom Original_LF__DOT__Lists_LF_Lists_NatList_test__rev2 :
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__Lists_LF_Lists_NatList_rev Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil)
    Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil

-- rev_involutive : forall l : natlist, rev (rev l) = l (Admitted in Original.v)
axiom Original_LF__DOT__Lists_LF_Lists_NatList_rev__involutive :
  ∀ (l : Original_LF__DOT__Lists_LF_Lists_NatList_natlist),
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__Lists_LF_Lists_NatList_rev (Original_LF__DOT__Lists_LF_Lists_NatList_rev l))
    l

-- ============================================================================
-- Poly module - polymorphic prod, fst, snd
-- ============================================================================

-- Poly prod type (product type)
inductive Original_LF__DOT__Poly_LF_Poly_prod (X Y : Type) : Type where
  | pair : X → Y → Original_LF__DOT__Poly_LF_Poly_prod X Y

def Original_LF__DOT__Poly_LF_Poly_prod_pair := @Original_LF__DOT__Poly_LF_Poly_prod.pair

-- fst function
def Original_LF__DOT__Poly_LF_Poly_fst {X Y : Type} (p : Original_LF__DOT__Poly_LF_Poly_prod X Y) : X :=
  match p with
  | Original_LF__DOT__Poly_LF_Poly_prod.pair x _ => x

-- snd function
def Original_LF__DOT__Poly_LF_Poly_snd {X Y : Type} (p : Original_LF__DOT__Poly_LF_Poly_prod X Y) : Y :=
  match p with
  | Original_LF__DOT__Poly_LF_Poly_prod.pair _ y => y

-- id type (wraps a natural number)
inductive Original_LF__DOT__Lists_LF_Lists_id : Type where
  | Id : nat → Original_LF__DOT__Lists_LF_Lists_id

-- eqb_id function (equality test for id)
def Original_LF__DOT__Lists_LF_Lists_eqb__id (x1 x2 : Original_LF__DOT__Lists_LF_Lists_id) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match x1, x2 with
  | Original_LF__DOT__Lists_LF_Lists_id.Id n1, Original_LF__DOT__Lists_LF_Lists_id.Id n2 => 
      Original_LF__DOT__Basics_LF_Basics_eqb n1 n2

-- partial_map
inductive Original_LF__DOT__Lists_LF_Lists_partial__map : Type where
  | empty : Original_LF__DOT__Lists_LF_Lists_partial__map
  | record : Original_LF__DOT__Lists_LF_Lists_id → nat → Original_LF__DOT__Lists_LF_Lists_partial__map → Original_LF__DOT__Lists_LF_Lists_partial__map

-- find function
def Original_LF__DOT__Lists_LF_Lists_find (x : Original_LF__DOT__Lists_LF_Lists_id) (d : Original_LF__DOT__Lists_LF_Lists_partial__map) : Original_LF__DOT__Lists_LF_Lists_NatList_natoption :=
  match d with
  | Original_LF__DOT__Lists_LF_Lists_partial__map.empty =>
    Original_LF__DOT__Lists_LF_Lists_NatList_natoption.None
  | Original_LF__DOT__Lists_LF_Lists_partial__map.record y v d' =>
    match Original_LF__DOT__Lists_LF_Lists_eqb__id x y with
    | Original_LF__DOT__Basics_LF_Basics_bool.true => Original_LF__DOT__Lists_LF_Lists_NatList_natoption.Some v
    | Original_LF__DOT__Basics_LF_Basics_bool.false => Original_LF__DOT__Lists_LF_Lists_find x d'

-- update function
def Original_LF__DOT__Lists_LF_Lists_update
    (d : Original_LF__DOT__Lists_LF_Lists_partial__map)
    (x : Original_LF__DOT__Lists_LF_Lists_id)
    (value : nat)
    : Original_LF__DOT__Lists_LF_Lists_partial__map :=
  Original_LF__DOT__Lists_LF_Lists_partial__map.record x value d

-- update_eq theorem (Admitted in Original.v)
axiom Original_LF__DOT__Lists_LF_Lists_update__eq :
  ∀ (d : Original_LF__DOT__Lists_LF_Lists_partial__map)
    (x : Original_LF__DOT__Lists_LF_Lists_id)
    (v : nat),
    Corelib_Init_Logic_eq
      (Original_LF__DOT__Lists_LF_Lists_find x (Original_LF__DOT__Lists_LF_Lists_update d x v))
      (Original_LF__DOT__Lists_LF_Lists_NatList_Some v)

-- app_nil_r theorem (Admitted in Original.v)
axiom Original_LF__DOT__Lists_LF_Lists_NatList_app__nil__r :
  ∀ (l : Original_LF__DOT__Lists_LF_Lists_NatList_natlist),
    Corelib_Init_Logic_eq
      (Original_LF__DOT__Lists_LF_Lists_NatList_app l Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil)
      l

-- ============================================================================
-- AltAuto module
-- ============================================================================

-- eq_example1' is Admitted in the original
axiom Original_LF__DOT__AltAuto_LF_AltAuto_eq__example1' :
  ∀ (A B C : Sort _) (f : A → B) (g : B → C) (x : A) (y : B),
    Corelib_Init_Logic_eq y (f x) → Corelib_Init_Logic_eq (g y) (g (f x))
