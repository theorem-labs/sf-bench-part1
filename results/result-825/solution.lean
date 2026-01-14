-- Complete Lean translation for break_ignore and all dependencies

-- Boolean type (custom to match Rocq's bool)
-- Use a name that won't conflict with Lean's Bool
inductive RocqBool : Type where
  | RocqTrue : RocqBool
  | RocqFalse : RocqBool

-- Aliases matching what Rocq expects
abbrev mybool := RocqBool
abbrev mybool_mytrue := RocqBool.RocqTrue
abbrev mybool_myfalse := RocqBool.RocqFalse

-- Ascii type
inductive Ascii_ascii : Type where
  | Ascii : mybool → mybool → mybool → mybool → mybool → mybool → mybool → mybool → Ascii_ascii

-- Alias for Ascii constructor
abbrev Ascii_Ascii := Ascii_ascii.Ascii

-- String type (matching Rocq's String.string)
inductive String_string : Type where
  | EmptyString : String_string
  | String : Ascii_ascii → String_string → String_string

-- Nat type (matching Rocq's nat)
inductive nat : Type where
  | O : nat
  | S : nat → nat

-- Maps (total_map)
def Original_LF__DOT__Maps_LF_Maps_total__map (A : Type) : Type := String_string → A

-- State type
def Original_LF__DOT__Imp_LF_Imp_state : Type := Original_LF__DOT__Maps_LF_Maps_total__map nat

-- Arithmetic expressions
inductive Original_LF__DOT__Imp_LF_Imp_aexp : Type where
  | ANum : nat → Original_LF__DOT__Imp_LF_Imp_aexp
  | AId : String_string → Original_LF__DOT__Imp_LF_Imp_aexp
  | APlus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp
  | AMinus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp
  | AMult : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp

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

-- Result type for BreakImp
inductive Original_LF__DOT__Imp_LF_Imp_BreakImp_result : Type where
  | SContinue : Original_LF__DOT__Imp_LF_Imp_BreakImp_result
  | SBreak : Original_LF__DOT__Imp_LF_Imp_BreakImp_result

-- Extracting constructors
def Original_LF__DOT__Imp_LF_Imp_BreakImp_SContinue := Original_LF__DOT__Imp_LF_Imp_BreakImp_result.SContinue
def Original_LF__DOT__Imp_LF_Imp_BreakImp_SBreak := Original_LF__DOT__Imp_LF_Imp_BreakImp_result.SBreak

-- Commands for BreakImp
inductive Original_LF__DOT__Imp_LF_Imp_BreakImp_com : Type where
  | CSkip : Original_LF__DOT__Imp_LF_Imp_BreakImp_com
  | CBreak : Original_LF__DOT__Imp_LF_Imp_BreakImp_com
  | CAsgn : String_string → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_BreakImp_com
  | CSeq : Original_LF__DOT__Imp_LF_Imp_BreakImp_com → Original_LF__DOT__Imp_LF_Imp_BreakImp_com → Original_LF__DOT__Imp_LF_Imp_BreakImp_com
  | CIf : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_BreakImp_com → Original_LF__DOT__Imp_LF_Imp_BreakImp_com → Original_LF__DOT__Imp_LF_Imp_BreakImp_com
  | CWhile : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_BreakImp_com → Original_LF__DOT__Imp_LF_Imp_BreakImp_com

-- Extract com constructors
def Original_LF__DOT__Imp_LF_Imp_BreakImp_CSkip := Original_LF__DOT__Imp_LF_Imp_BreakImp_com.CSkip
def Original_LF__DOT__Imp_LF_Imp_BreakImp_CBreak := Original_LF__DOT__Imp_LF_Imp_BreakImp_com.CBreak
def Original_LF__DOT__Imp_LF_Imp_BreakImp_CAsgn := Original_LF__DOT__Imp_LF_Imp_BreakImp_com.CAsgn
def Original_LF__DOT__Imp_LF_Imp_BreakImp_CSeq := Original_LF__DOT__Imp_LF_Imp_BreakImp_com.CSeq
def Original_LF__DOT__Imp_LF_Imp_BreakImp_CIf := Original_LF__DOT__Imp_LF_Imp_BreakImp_com.CIf
def Original_LF__DOT__Imp_LF_Imp_BreakImp_CWhile := Original_LF__DOT__Imp_LF_Imp_BreakImp_com.CWhile

-- Evaluation relation for BreakImp (only E_Skip constructor as in Original)
inductive Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval :
  Original_LF__DOT__Imp_LF_Imp_BreakImp_com →
  Original_LF__DOT__Imp_LF_Imp_state →
  Original_LF__DOT__Imp_LF_Imp_BreakImp_result →
  Original_LF__DOT__Imp_LF_Imp_state → Prop where
  | E_Skip : ∀ (st : Original_LF__DOT__Imp_LF_Imp_state),
      Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval
        Original_LF__DOT__Imp_LF_Imp_BreakImp_com.CSkip
        st
        Original_LF__DOT__Imp_LF_Imp_BreakImp_result.SContinue
        st

-- True type as Prop (will be exported as SProp in Rocq)
-- Use Lean's built-in True and create an alias
def myTrue : Prop := True
def True_I : myTrue := True.intro

-- False type
inductive myFalse : Prop where

-- Alias for False
abbrev Rocq_False := myFalse

-- List type
inductive list (A : Type) : Type where
  | nil : list A
  | cons : A → list A → list A

-- List.In predicate
def List_In {A : Type} (a : A) : list A → Prop
  | list.nil => False
  | list.cons h t => a = h ∨ List_In a t

-- Logic.not - needs to be Prop -> Prop but exports as SProp -> SProp
def Logic_not (P : Prop) : Prop := P → myFalse

-- Equality type in Prop (will become SProp in Rocq) - Type version
inductive Corelib_Init_Logic_eq {A : Type} (a : A) : A → Prop where
  | refl : Corelib_Init_Logic_eq a a

-- Equality type in Prop (for Prop -> Prop) - Prop version
inductive Corelib_Init_Logic_eq_Prop {A : Prop} (a : A) : A → Prop where
  | refl : Corelib_Init_Logic_eq_Prop a a

-- The main axiom: break_ignore
-- Theorem break_ignore : forall c st st' s,
--      st =[ break; c ]=> st' / s ->
--      st = st'.
axiom Original_LF__DOT__Imp_LF_Imp_BreakImp_break__ignore :
  ∀ (c : Original_LF__DOT__Imp_LF_Imp_BreakImp_com)
    (st st' : Original_LF__DOT__Imp_LF_Imp_state)
    (s : Original_LF__DOT__Imp_LF_Imp_BreakImp_result),
    Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval
      (Original_LF__DOT__Imp_LF_Imp_BreakImp_com.CSeq Original_LF__DOT__Imp_LF_Imp_BreakImp_com.CBreak c)
      st
      s
      st' →
    Corelib_Init_Logic_eq st st'
