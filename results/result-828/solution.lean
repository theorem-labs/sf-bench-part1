-- Complete Lean translation for ceval_deterministic and all dependencies

-- Boolean type (custom to match Rocq's bool)
inductive mybool : Type where
  | bool_true : mybool
  | bool_false : mybool

-- Aliases for export
def bool_true := mybool.bool_true
def bool_false := mybool.bool_false

-- Ascii type with named fields for proper export
structure Ascii_ascii : Type where
  b0 : mybool
  b1 : mybool
  b2 : mybool
  b3 : mybool
  b4 : mybool
  b5 : mybool
  b6 : mybool
  b7 : mybool

-- Alias for Ascii constructor
def Ascii_ascii_Ascii (b0 b1 b2 b3 b4 b5 b6 b7 : mybool) : Ascii_ascii :=
  { b0 := b0, b1 := b1, b2 := b2, b3 := b3, b4 := b4, b5 := b5, b6 := b6, b7 := b7 }

-- String type (matching Rocq's String.string)
inductive String_string : Type where
  | EmptyString : String_string
  | String : Ascii_ascii → String_string → String_string

-- Constructor aliases for export
def String_string_EmptyString := String_string.EmptyString
def String_string_String := String_string.String

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
-- Use inductive to create our own True that can be exported
inductive RocqTrue : Prop where
  | I : RocqTrue

-- Aliases for export
def myTrue : Prop := RocqTrue
def True_I : myTrue := RocqTrue.I

-- False type
inductive myFalse : Prop where

-- Alias for False
abbrev Rocq_False := myFalse

-- Equality type in Prop (will become SProp in Rocq) - Type version
inductive Corelib_Init_Logic_eq {A : Type} (a : A) : A → Prop where
  | refl : Corelib_Init_Logic_eq a a

-- Equality type in Prop (for SProp -> SProp version in Rocq)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} (a : A) : A → Prop where
  | refl : Corelib_Init_Logic_eq_Prop a a

-- And type (matching Coq and) - this is what the checker expects
structure and (P Q : Prop) : Prop where
  intro ::
  left : P
  right : Q

-- The main axiom: ceval_deterministic
-- Theorem ceval_deterministic: forall (c:com) st st1 st2 s1 s2,
--      st =[ c ]=> st1 / s1 ->
--      st =[ c ]=> st2 / s2 ->
--      st1 = st2 /\ s1 = s2.
-- ceval : com -> state -> result -> state -> Prop
-- so st =[ c ]=> st1 / s1 means ceval c st s1 st1
axiom Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval__deterministic :
  ∀ (c : Original_LF__DOT__Imp_LF_Imp_BreakImp_com)
    (st : Original_LF__DOT__Imp_LF_Imp_state)
    (st1 : Original_LF__DOT__Imp_LF_Imp_state)
    (st2 : Original_LF__DOT__Imp_LF_Imp_state)
    (s1 s2 : Original_LF__DOT__Imp_LF_Imp_BreakImp_result),
    Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval c st s1 st1 →
    Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval c st s2 st2 →
    and (Corelib_Init_Logic_eq st1 st2) (Corelib_Init_Logic_eq s1 s2)
