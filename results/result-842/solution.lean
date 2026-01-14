-- Lean translation for while_break_true and all dependencies

set_option linter.all false

-- Boolean type (using custom names to avoid conflicts)
inductive Coq_bool : Type where
  | Coq_true : Coq_bool
  | Coq_false : Coq_bool

-- Aliases for bool - use abbrev to avoid redefinition issues
abbrev mybool := Coq_bool
abbrev mybool_mytrue := Coq_bool.Coq_true
abbrev mybool_myfalse := Coq_bool.Coq_false

-- Re-export with expected names
def Coq_bool_Coq_true := Coq_bool.Coq_true
def Coq_bool_Coq_false := Coq_bool.Coq_false

-- Natural numbers
inductive Coq_nat : Type where
  | O : Coq_nat
  | S : Coq_nat → Coq_nat

-- Aliases for nat
def nat := Coq_nat
def nat_O := Coq_nat.O
def nat_S := Coq_nat.S

-- Ascii (8 bools)
inductive Ascii_ascii : Type where
  | Ascii : Coq_bool → Coq_bool → Coq_bool → Coq_bool → Coq_bool → Coq_bool → Coq_bool → Coq_bool → Ascii_ascii

def Ascii_Ascii := Ascii_ascii.Ascii

-- String type
inductive String_string : Type where
  | EmptyString : String_string
  | String : Ascii_ascii → String_string → String_string

def String_string_EmptyString := String_string.EmptyString
def String_string_String := String_string.String

-- total_map
def Original_LF__DOT__Maps_LF_Maps_total__map (A : Type) := String_string → A

-- state
def Original_LF__DOT__Imp_LF_Imp_state := Original_LF__DOT__Maps_LF_Maps_total__map Coq_nat

-- nat operations
def nat_add : Coq_nat → Coq_nat → Coq_nat
  | Coq_nat.O, m => m
  | Coq_nat.S n, m => Coq_nat.S (nat_add n m)

def nat_sub : Coq_nat → Coq_nat → Coq_nat
  | n, Coq_nat.O => n
  | Coq_nat.O, Coq_nat.S _ => Coq_nat.O
  | Coq_nat.S n, Coq_nat.S m => nat_sub n m

def nat_mul : Coq_nat → Coq_nat → Coq_nat
  | Coq_nat.O, _ => Coq_nat.O
  | Coq_nat.S n, m => nat_add m (nat_mul n m)

def nat_eqb : Coq_nat → Coq_nat → Coq_bool
  | Coq_nat.O, Coq_nat.O => Coq_bool.Coq_true
  | Coq_nat.S n, Coq_nat.S m => nat_eqb n m
  | _, _ => Coq_bool.Coq_false

def nat_leb : Coq_nat → Coq_nat → Coq_bool
  | Coq_nat.O, _ => Coq_bool.Coq_true
  | Coq_nat.S _, Coq_nat.O => Coq_bool.Coq_false
  | Coq_nat.S n, Coq_nat.S m => nat_leb n m

def bool_negb : Coq_bool → Coq_bool
  | Coq_bool.Coq_true => Coq_bool.Coq_false
  | Coq_bool.Coq_false => Coq_bool.Coq_true

def bool_andb : Coq_bool → Coq_bool → Coq_bool
  | Coq_bool.Coq_true, b => b
  | Coq_bool.Coq_false, _ => Coq_bool.Coq_false

-- String equality
def Bool_eqb : Coq_bool → Coq_bool → Coq_bool
  | Coq_bool.Coq_true, Coq_bool.Coq_true => Coq_bool.Coq_true
  | Coq_bool.Coq_false, Coq_bool.Coq_false => Coq_bool.Coq_true
  | _, _ => Coq_bool.Coq_false

def Ascii_eqb : Ascii_ascii → Ascii_ascii → Coq_bool
  | Ascii_ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7, Ascii_ascii.Ascii c0 c1 c2 c3 c4 c5 c6 c7 =>
    match Bool_eqb b0 c0 with
    | Coq_bool.Coq_false => Coq_bool.Coq_false
    | Coq_bool.Coq_true => match Bool_eqb b1 c1 with
      | Coq_bool.Coq_false => Coq_bool.Coq_false
      | Coq_bool.Coq_true => match Bool_eqb b2 c2 with
        | Coq_bool.Coq_false => Coq_bool.Coq_false
        | Coq_bool.Coq_true => match Bool_eqb b3 c3 with
          | Coq_bool.Coq_false => Coq_bool.Coq_false
          | Coq_bool.Coq_true => match Bool_eqb b4 c4 with
            | Coq_bool.Coq_false => Coq_bool.Coq_false
            | Coq_bool.Coq_true => match Bool_eqb b5 c5 with
              | Coq_bool.Coq_false => Coq_bool.Coq_false
              | Coq_bool.Coq_true => match Bool_eqb b6 c6 with
                | Coq_bool.Coq_false => Coq_bool.Coq_false
                | Coq_bool.Coq_true => Bool_eqb b7 c7

def String_eqb : String_string → String_string → Coq_bool
  | String_string.EmptyString, String_string.EmptyString => Coq_bool.Coq_true
  | String_string.String c1 s1, String_string.String c2 s2 =>
    match Ascii_eqb c1 c2 with
    | Coq_bool.Coq_false => Coq_bool.Coq_false
    | Coq_bool.Coq_true => String_eqb s1 s2
  | _, _ => Coq_bool.Coq_false

-- aexp
inductive Original_LF__DOT__Imp_LF_Imp_aexp : Type where
  | ANum : Coq_nat → Original_LF__DOT__Imp_LF_Imp_aexp
  | AId : String_string → Original_LF__DOT__Imp_LF_Imp_aexp
  | APlus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp
  | AMinus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp
  | AMult : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp

def Original_LF__DOT__Imp_LF_Imp_aexp_ANum := Original_LF__DOT__Imp_LF_Imp_aexp.ANum
def Original_LF__DOT__Imp_LF_Imp_aexp_AId := Original_LF__DOT__Imp_LF_Imp_aexp.AId
def Original_LF__DOT__Imp_LF_Imp_aexp_APlus := Original_LF__DOT__Imp_LF_Imp_aexp.APlus
def Original_LF__DOT__Imp_LF_Imp_aexp_AMinus := Original_LF__DOT__Imp_LF_Imp_aexp.AMinus
def Original_LF__DOT__Imp_LF_Imp_aexp_AMult := Original_LF__DOT__Imp_LF_Imp_aexp.AMult

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

def Original_LF__DOT__Imp_LF_Imp_bexp_BTrue := Original_LF__DOT__Imp_LF_Imp_bexp.BTrue
def Original_LF__DOT__Imp_LF_Imp_bexp_BFalse := Original_LF__DOT__Imp_LF_Imp_bexp.BFalse
def Original_LF__DOT__Imp_LF_Imp_bexp_BEq := Original_LF__DOT__Imp_LF_Imp_bexp.BEq
def Original_LF__DOT__Imp_LF_Imp_bexp_BNeq := Original_LF__DOT__Imp_LF_Imp_bexp.BNeq
def Original_LF__DOT__Imp_LF_Imp_bexp_BLe := Original_LF__DOT__Imp_LF_Imp_bexp.BLe
def Original_LF__DOT__Imp_LF_Imp_bexp_BGt := Original_LF__DOT__Imp_LF_Imp_bexp.BGt
def Original_LF__DOT__Imp_LF_Imp_bexp_BNot := Original_LF__DOT__Imp_LF_Imp_bexp.BNot
def Original_LF__DOT__Imp_LF_Imp_bexp_BAnd := Original_LF__DOT__Imp_LF_Imp_bexp.BAnd

-- aeval
def Original_LF__DOT__Imp_LF_Imp_aeval (st : Original_LF__DOT__Imp_LF_Imp_state) : Original_LF__DOT__Imp_LF_Imp_aexp → Coq_nat
  | Original_LF__DOT__Imp_LF_Imp_aexp.ANum n => n
  | Original_LF__DOT__Imp_LF_Imp_aexp.AId x => st x
  | Original_LF__DOT__Imp_LF_Imp_aexp.APlus a1 a2 => nat_add (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
  | Original_LF__DOT__Imp_LF_Imp_aexp.AMinus a1 a2 => nat_sub (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
  | Original_LF__DOT__Imp_LF_Imp_aexp.AMult a1 a2 => nat_mul (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)

-- beval
def Original_LF__DOT__Imp_LF_Imp_beval (st : Original_LF__DOT__Imp_LF_Imp_state) : Original_LF__DOT__Imp_LF_Imp_bexp → Coq_bool
  | Original_LF__DOT__Imp_LF_Imp_bexp.BTrue => Coq_bool.Coq_true
  | Original_LF__DOT__Imp_LF_Imp_bexp.BFalse => Coq_bool.Coq_false
  | Original_LF__DOT__Imp_LF_Imp_bexp.BEq a1 a2 => nat_eqb (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
  | Original_LF__DOT__Imp_LF_Imp_bexp.BNeq a1 a2 => bool_negb (nat_eqb (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2))
  | Original_LF__DOT__Imp_LF_Imp_bexp.BLe a1 a2 => nat_leb (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
  | Original_LF__DOT__Imp_LF_Imp_bexp.BGt a1 a2 => bool_negb (nat_leb (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2))
  | Original_LF__DOT__Imp_LF_Imp_bexp.BNot b1 => bool_negb (Original_LF__DOT__Imp_LF_Imp_beval st b1)
  | Original_LF__DOT__Imp_LF_Imp_bexp.BAnd b1 b2 => bool_andb (Original_LF__DOT__Imp_LF_Imp_beval st b1) (Original_LF__DOT__Imp_LF_Imp_beval st b2)

-- Result type
inductive Original_LF__DOT__Imp_LF_Imp_BreakImp_result : Type where
  | SContinue : Original_LF__DOT__Imp_LF_Imp_BreakImp_result
  | SBreak : Original_LF__DOT__Imp_LF_Imp_BreakImp_result

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

def Original_LF__DOT__Imp_LF_Imp_BreakImp_CSkip := Original_LF__DOT__Imp_LF_Imp_BreakImp_com.CSkip
def Original_LF__DOT__Imp_LF_Imp_BreakImp_CBreak := Original_LF__DOT__Imp_LF_Imp_BreakImp_com.CBreak
def Original_LF__DOT__Imp_LF_Imp_BreakImp_CAsgn := Original_LF__DOT__Imp_LF_Imp_BreakImp_com.CAsgn
def Original_LF__DOT__Imp_LF_Imp_BreakImp_CSeq := Original_LF__DOT__Imp_LF_Imp_BreakImp_com.CSeq
def Original_LF__DOT__Imp_LF_Imp_BreakImp_CIf := Original_LF__DOT__Imp_LF_Imp_BreakImp_com.CIf
def Original_LF__DOT__Imp_LF_Imp_BreakImp_CWhile := Original_LF__DOT__Imp_LF_Imp_BreakImp_com.CWhile

-- Evaluation relation (only E_Skip needed for type completeness)
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

-- Equality in Prop (will become SProp in Rocq) - Type version
inductive Corelib_Init_Logic_eq {A : Type} (a : A) : A → Prop where
  | refl : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a := Corelib_Init_Logic_eq.refl

-- Equality in Prop - Prop version (for SProp arguments)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} (a : A) : A → Prop where
  | refl : Corelib_Init_Logic_eq_Prop a a

def Corelib_Init_Logic_eq_Prop_refl {A : Prop} (a : A) : Corelib_Init_Logic_eq_Prop a a := Corelib_Init_Logic_eq_Prop.refl

-- Existential type
inductive ex {A : Type} (P : A → Prop) : Prop where
  | intro (w : A) (h : P w) : ex P

def ex_intro {A : Type} {P : A → Prop} (w : A) (h : P w) : ex P := ex.intro w h

-- True type (in Prop, will become SProp)
inductive True_ : Prop where
  | I : True_

def True_I : True_ := True_.I

-- The main axiom: while_break_true
-- forall b c st st',
--   st =[ while b do c end ]=> st' / SContinue ->
--   beval st' b = true ->
--   exists st'', st'' =[ c ]=> st' / SBreak
axiom Original_LF__DOT__Imp_LF_Imp_BreakImp_while__break__true :
  ∀ (b : Original_LF__DOT__Imp_LF_Imp_bexp)
    (c : Original_LF__DOT__Imp_LF_Imp_BreakImp_com)
    (st st' : Original_LF__DOT__Imp_LF_Imp_state),
    Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval
      (Original_LF__DOT__Imp_LF_Imp_BreakImp_com.CWhile b c) st
      Original_LF__DOT__Imp_LF_Imp_BreakImp_result.SContinue st' →
    Corelib_Init_Logic_eq (Original_LF__DOT__Imp_LF_Imp_beval st' b) Coq_bool.Coq_true →
    ex (fun st'' : Original_LF__DOT__Imp_LF_Imp_state =>
      Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval c st''
        Original_LF__DOT__Imp_LF_Imp_BreakImp_result.SBreak st')
