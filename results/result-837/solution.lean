/-
  Lean translation of Imp language definitions for ceval_example1
  Matches the Rocq definitions exactly for isomorphism checking.
-/

set_option linter.all false

-- Define our own bool type matching Rocq's bool
-- Using prefix to avoid name clash with Lean's built-in bool
inductive bool_ : Type where
  | true_ : bool_
  | false_ : bool_

-- Aliases for the checker
def bool__true_ := bool_.true_
def bool__false_ := bool_.false_

-- Need both bool and bool_ exported (Mybool will become bool via sed)
def Mybool := bool_

-- True proposition (we need this for SProp)
inductive True_ : Prop where
  | I : True_

-- I constructor alias
def I_ := True_.I

-- Alias for True that matches Rocq naming (use different name, fix in .out)
def MyTrue := True_
def MyTrue_I := True_.I

-- False proposition
inductive False_ : Prop where

-- Alias
def MyFalse := False_

-- List type
inductive list (A : Type) : Type where
  | list_nil : list A
  | list_cons : A → list A → list A

def nil {A : Type} := @list.list_nil A
def cons {A : Type} := @list.list_cons A

-- Equality type (for Corelib.Init.Logic.eq)
inductive Corelib_Init_Logic_eq {A : Sort u} (a : A) : A → Prop where
  | refl : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {A : Sort u} (a : A) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl

-- Specialized version for Prop
def Corelib_Init_Logic_eq_Prop (A : Prop) (a : A) (b : A) : Prop :=
  Corelib_Init_Logic_eq a b

def Corelib_Init_Logic_eq_refl_Prop (A : Prop) (a : A) : Corelib_Init_Logic_eq_Prop A a a :=
  Corelib_Init_Logic_eq.refl

-- or type
inductive or_ (A B : Prop) : Prop where
  | or_introl : A → or_ A B
  | or_intror : B → or_ A B

-- List membership predicate
def List_In {A : Type} (a : A) : list A → Prop
  | list.list_nil => False_
  | list.list_cons x xs => or_ (@Corelib_Init_Logic_eq A a x) (List_In a xs)

-- Logic.not
def Logic_not (P : Prop) : Prop := P → False_

-- Option type
inductive option (A : Type) : Type where
  | None : option A
  | Some : A → option A

def None {A : Type} := @option.None A
def Some {A : Type} := @option.Some A

-- Relation type
def Original_LF_Rel_relation (X : Type) : Type := X → X → Prop

-- Natural numbers matching Rocq's nat
inductive nat_ : Type where
  | O_ : nat_
  | S_ : nat_ → nat_

-- Aliases for nat with proper names
def nat := nat_
def nat_O := nat_.O_
def nat_S := nat_.S_
def _0 := nat_.O_
def S := nat_.S_

-- Nat operations
def nat_add : nat_ → nat_ → nat_
  | nat_.O_, m => m
  | nat_.S_ n, m => nat_.S_ (nat_add n m)

def nat_sub : nat_ → nat_ → nat_
  | n, nat_.O_ => n
  | nat_.O_, nat_.S_ _ => nat_.O_
  | nat_.S_ n, nat_.S_ m => nat_sub n m

def nat_mul : nat_ → nat_ → nat_
  | nat_.O_, _ => nat_.O_
  | nat_.S_ n, m => nat_add m (nat_mul n m)

def nat_eqb : nat_ → nat_ → bool_
  | nat_.O_, nat_.O_ => bool_.true_
  | nat_.S_ n, nat_.S_ m => nat_eqb n m
  | _, _ => bool_.false_

def nat_leb : nat_ → nat_ → bool_
  | nat_.O_, _ => bool_.true_
  | nat_.S_ _, nat_.O_ => bool_.false_
  | nat_.S_ n, nat_.S_ m => nat_leb n m

def bool_negb : bool_ → bool_
  | bool_.true_ => bool_.false_
  | bool_.false_ => bool_.true_

def bool_andb : bool_ → bool_ → bool_
  | bool_.true_, b => b
  | bool_.false_, _ => bool_.false_

def bool_eqb : bool_ → bool_ → bool_
  | bool_.true_, bool_.true_ => bool_.true_
  | bool_.false_, bool_.false_ => bool_.true_
  | _, _ => bool_.false_

-- Aliases for nat operations with expected names (as definitions that match Rocq's)
def Nat_add (n m : nat_) : nat_ := nat_add n m
def Nat_sub (n m : nat_) : nat_ := nat_sub n m
def Nat_mul (n m : nat_) : nat_ := nat_mul n m
def Nat_eqb (n m : nat_) : bool_ := nat_eqb n m
def Nat_leb (n m : nat_) : bool_ := nat_leb n m
def Nat_pred (n : nat_) : nat_ :=
  match n with
  | nat_.O_ => nat_.O_
  | nat_.S_ m => m
def negb := bool_negb
def andb := bool_andb

-- True proposition (for SProp compatibility)
-- We can't define 'True' as it's reserved, so just use the built-in one
-- This will be exported as True

-- Define Ascii as 8 bools (like Rocq's Ascii.ascii)
inductive Ascii_ascii : Type where
  | Ascii : bool_ → bool_ → bool_ → bool_ → bool_ → bool_ → bool_ → bool_ → Ascii_ascii

-- Alias for checker compatibility (Ascii_Ascii is the constructor)
def Ascii_Ascii := Ascii_ascii.Ascii

-- Define equality on Ascii
def Ascii_eqb : Ascii_ascii → Ascii_ascii → bool_
  | Ascii_ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7, Ascii_ascii.Ascii c0 c1 c2 c3 c4 c5 c6 c7 =>
    bool_andb (bool_eqb b0 c0)
      (bool_andb (bool_eqb b1 c1)
        (bool_andb (bool_eqb b2 c2)
          (bool_andb (bool_eqb b3 c3)
            (bool_andb (bool_eqb b4 c4)
              (bool_andb (bool_eqb b5 c5)
                (bool_andb (bool_eqb b6 c6)
                  (bool_eqb b7 c7)))))))

-- String type (like Rocq's String.string)
inductive String_string : Type where
  | EmptyString : String_string
  | String : Ascii_ascii → String_string → String_string

-- String equality
def String_eqb : String_string → String_string → bool_
  | String_string.EmptyString, String_string.EmptyString => bool_.true_
  | String_string.String c1 s1, String_string.String c2 s2 =>
    bool_andb (Ascii_eqb c1 c2) (String_eqb s1 s2)
  | _, _ => bool_.false_

-- total_map type (function from string to A)
def Original_LF__DOT__Maps_LF_Maps_total__map (A : Type) := String_string → A

-- t_empty: create empty total map with default value
def Original_LF__DOT__Maps_LF_Maps_t__empty {A : Type} (v : A) : Original_LF__DOT__Maps_LF_Maps_total__map A :=
  fun _ => v

-- t_update: update a total map
def Original_LF__DOT__Maps_LF_Maps_t__update {A : Type} (m : Original_LF__DOT__Maps_LF_Maps_total__map A)
    (x : String_string) (v : A) : Original_LF__DOT__Maps_LF_Maps_total__map A :=
  fun x' => match String_eqb x x' with
    | bool_.true_ => v
    | bool_.false_ => m x'

-- State is total_map nat_
def Original_LF__DOT__Imp_LF_Imp_state := Original_LF__DOT__Maps_LF_Maps_total__map nat_

-- Helper for building ASCII characters
-- 'X' = 88 = 0b01011000, LSB first: 0,0,0,1,1,0,1,0
def charX : Ascii_ascii := Ascii_ascii.Ascii bool_.false_ bool_.false_ bool_.false_ bool_.true_ bool_.true_ bool_.false_ bool_.true_ bool_.false_
-- 'Y' = 89 = 0b01011001, LSB first: 1,0,0,1,1,0,1,0
def charY : Ascii_ascii := Ascii_ascii.Ascii bool_.true_ bool_.false_ bool_.false_ bool_.true_ bool_.true_ bool_.false_ bool_.true_ bool_.false_
-- 'Z' = 90 = 0b01011010, LSB first: 0,1,0,1,1,0,1,0
def charZ : Ascii_ascii := Ascii_ascii.Ascii bool_.false_ bool_.true_ bool_.false_ bool_.true_ bool_.true_ bool_.false_ bool_.true_ bool_.false_

-- Variables X, Y, Z
def Original_LF__DOT__Imp_LF_Imp_X : String_string := String_string.String charX String_string.EmptyString
def Original_LF__DOT__Imp_LF_Imp_Y : String_string := String_string.String charY String_string.EmptyString
def Original_LF__DOT__Imp_LF_Imp_Z : String_string := String_string.String charZ String_string.EmptyString

-- Arithmetic expressions (matches Original.LF_DOT_Imp.LF.Imp.aexp)
inductive Original_LF__DOT__Imp_LF_Imp_aexp : Type where
  | ANum : nat_ → Original_LF__DOT__Imp_LF_Imp_aexp
  | AId : String_string → Original_LF__DOT__Imp_LF_Imp_aexp
  | APlus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp
  | AMinus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp
  | AMult : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp

-- Boolean expressions (matches Original.LF_DOT_Imp.LF.Imp.bexp)
inductive Original_LF__DOT__Imp_LF_Imp_bexp : Type where
  | BTrue : Original_LF__DOT__Imp_LF_Imp_bexp
  | BFalse : Original_LF__DOT__Imp_LF_Imp_bexp
  | BEq : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BNeq : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BLe : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BGt : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BNot : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BAnd : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp

-- Constructor aliases for aexp
def Original_LF__DOT__Imp_LF_Imp_ANum := Original_LF__DOT__Imp_LF_Imp_aexp.ANum
def Original_LF__DOT__Imp_LF_Imp_AId := Original_LF__DOT__Imp_LF_Imp_aexp.AId
def Original_LF__DOT__Imp_LF_Imp_APlus := Original_LF__DOT__Imp_LF_Imp_aexp.APlus
def Original_LF__DOT__Imp_LF_Imp_AMinus := Original_LF__DOT__Imp_LF_Imp_aexp.AMinus
def Original_LF__DOT__Imp_LF_Imp_AMult := Original_LF__DOT__Imp_LF_Imp_aexp.AMult

-- Constructor aliases for bexp
def Original_LF__DOT__Imp_LF_Imp_BTrue := Original_LF__DOT__Imp_LF_Imp_bexp.BTrue
def Original_LF__DOT__Imp_LF_Imp_BFalse := Original_LF__DOT__Imp_LF_Imp_bexp.BFalse
def Original_LF__DOT__Imp_LF_Imp_BEq := Original_LF__DOT__Imp_LF_Imp_bexp.BEq
def Original_LF__DOT__Imp_LF_Imp_BNeq := Original_LF__DOT__Imp_LF_Imp_bexp.BNeq
def Original_LF__DOT__Imp_LF_Imp_BLe := Original_LF__DOT__Imp_LF_Imp_bexp.BLe
def Original_LF__DOT__Imp_LF_Imp_BGt := Original_LF__DOT__Imp_LF_Imp_bexp.BGt
def Original_LF__DOT__Imp_LF_Imp_BNot := Original_LF__DOT__Imp_LF_Imp_bexp.BNot
def Original_LF__DOT__Imp_LF_Imp_BAnd := Original_LF__DOT__Imp_LF_Imp_bexp.BAnd

-- aeval: evaluates arithmetic expression in a state
def Original_LF__DOT__Imp_LF_Imp_aeval (st : Original_LF__DOT__Imp_LF_Imp_state) : Original_LF__DOT__Imp_LF_Imp_aexp → nat_
  | Original_LF__DOT__Imp_LF_Imp_aexp.ANum n => n
  | Original_LF__DOT__Imp_LF_Imp_aexp.AId x => st x
  | Original_LF__DOT__Imp_LF_Imp_aexp.APlus a1 a2 => nat_add (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
  | Original_LF__DOT__Imp_LF_Imp_aexp.AMinus a1 a2 => nat_sub (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
  | Original_LF__DOT__Imp_LF_Imp_aexp.AMult a1 a2 => nat_mul (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)

-- beval: evaluates boolean expression in a state
def Original_LF__DOT__Imp_LF_Imp_beval (st : Original_LF__DOT__Imp_LF_Imp_state) : Original_LF__DOT__Imp_LF_Imp_bexp → bool_
  | Original_LF__DOT__Imp_LF_Imp_bexp.BTrue => bool_.true_
  | Original_LF__DOT__Imp_LF_Imp_bexp.BFalse => bool_.false_
  | Original_LF__DOT__Imp_LF_Imp_bexp.BEq a1 a2 => nat_eqb (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
  | Original_LF__DOT__Imp_LF_Imp_bexp.BNeq a1 a2 => bool_negb (nat_eqb (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2))
  | Original_LF__DOT__Imp_LF_Imp_bexp.BLe a1 a2 => nat_leb (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
  | Original_LF__DOT__Imp_LF_Imp_bexp.BGt a1 a2 => bool_negb (nat_leb (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2))
  | Original_LF__DOT__Imp_LF_Imp_bexp.BNot b1 => bool_negb (Original_LF__DOT__Imp_LF_Imp_beval st b1)
  | Original_LF__DOT__Imp_LF_Imp_bexp.BAnd b1 b2 => bool_andb (Original_LF__DOT__Imp_LF_Imp_beval st b1) (Original_LF__DOT__Imp_LF_Imp_beval st b2)

-- empty_st: the empty state (maps everything to 0)
def Original_LF__DOT__Imp_LF_Imp_empty__st : Original_LF__DOT__Imp_LF_Imp_state :=
  Original_LF__DOT__Maps_LF_Maps_t__empty nat_.O_

-- Commands for the Repeat module (matches Original.LF_DOT_Auto.LF.Auto.Repeat.com)
inductive Original_LF__DOT__Auto_LF_Auto_Repeat_com : Type where
  | CSkip : Original_LF__DOT__Auto_LF_Auto_Repeat_com
  | CAsgn : String_string → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Auto_LF_Auto_Repeat_com
  | CSeq : Original_LF__DOT__Auto_LF_Auto_Repeat_com → Original_LF__DOT__Auto_LF_Auto_Repeat_com → Original_LF__DOT__Auto_LF_Auto_Repeat_com
  | CIf : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Auto_LF_Auto_Repeat_com → Original_LF__DOT__Auto_LF_Auto_Repeat_com → Original_LF__DOT__Auto_LF_Auto_Repeat_com
  | CWhile : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Auto_LF_Auto_Repeat_com → Original_LF__DOT__Auto_LF_Auto_Repeat_com
  | CRepeat : Original_LF__DOT__Auto_LF_Auto_Repeat_com → Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Auto_LF_Auto_Repeat_com

-- Constructor aliases for Repeat.com
def Original_LF__DOT__Auto_LF_Auto_Repeat_CSkip := Original_LF__DOT__Auto_LF_Auto_Repeat_com.CSkip
def Original_LF__DOT__Auto_LF_Auto_Repeat_CAsgn := Original_LF__DOT__Auto_LF_Auto_Repeat_com.CAsgn
def Original_LF__DOT__Auto_LF_Auto_Repeat_CSeq := Original_LF__DOT__Auto_LF_Auto_Repeat_com.CSeq
def Original_LF__DOT__Auto_LF_Auto_Repeat_CIf := Original_LF__DOT__Auto_LF_Auto_Repeat_com.CIf
def Original_LF__DOT__Auto_LF_Auto_Repeat_CWhile := Original_LF__DOT__Auto_LF_Auto_Repeat_com.CWhile
def Original_LF__DOT__Auto_LF_Auto_Repeat_CRepeat := Original_LF__DOT__Auto_LF_Auto_Repeat_com.CRepeat

-- ceval for Repeat module: big-step operational semantics as an inductive predicate
inductive Original_LF__DOT__Auto_LF_Auto_Repeat_ceval : Original_LF__DOT__Auto_LF_Auto_Repeat_com → Original_LF__DOT__Imp_LF_Imp_state → Original_LF__DOT__Imp_LF_Imp_state → Prop where
  | E_Skip : ∀ st, Original_LF__DOT__Auto_LF_Auto_Repeat_ceval Original_LF__DOT__Auto_LF_Auto_Repeat_com.CSkip st st
  | E_Asgn : ∀ st a n x,
      Original_LF__DOT__Imp_LF_Imp_aeval st a = n →
      Original_LF__DOT__Auto_LF_Auto_Repeat_ceval (Original_LF__DOT__Auto_LF_Auto_Repeat_com.CAsgn x a) st (Original_LF__DOT__Maps_LF_Maps_t__update st x n)
  | E_Seq : ∀ c1 c2 st st' st'',
      Original_LF__DOT__Auto_LF_Auto_Repeat_ceval c1 st st' →
      Original_LF__DOT__Auto_LF_Auto_Repeat_ceval c2 st' st'' →
      Original_LF__DOT__Auto_LF_Auto_Repeat_ceval (Original_LF__DOT__Auto_LF_Auto_Repeat_com.CSeq c1 c2) st st''
  | E_IfTrue : ∀ st st' b c1 c2,
      Original_LF__DOT__Imp_LF_Imp_beval st b = bool_.true_ →
      Original_LF__DOT__Auto_LF_Auto_Repeat_ceval c1 st st' →
      Original_LF__DOT__Auto_LF_Auto_Repeat_ceval (Original_LF__DOT__Auto_LF_Auto_Repeat_com.CIf b c1 c2) st st'
  | E_IfFalse : ∀ st st' b c1 c2,
      Original_LF__DOT__Imp_LF_Imp_beval st b = bool_.false_ →
      Original_LF__DOT__Auto_LF_Auto_Repeat_ceval c2 st st' →
      Original_LF__DOT__Auto_LF_Auto_Repeat_ceval (Original_LF__DOT__Auto_LF_Auto_Repeat_com.CIf b c1 c2) st st'
  | E_WhileFalse : ∀ b st c,
      Original_LF__DOT__Imp_LF_Imp_beval st b = bool_.false_ →
      Original_LF__DOT__Auto_LF_Auto_Repeat_ceval (Original_LF__DOT__Auto_LF_Auto_Repeat_com.CWhile b c) st st
  | E_WhileTrue : ∀ st st' st'' b c,
      Original_LF__DOT__Imp_LF_Imp_beval st b = bool_.true_ →
      Original_LF__DOT__Auto_LF_Auto_Repeat_ceval c st st' →
      Original_LF__DOT__Auto_LF_Auto_Repeat_ceval (Original_LF__DOT__Auto_LF_Auto_Repeat_com.CWhile b c) st' st'' →
      Original_LF__DOT__Auto_LF_Auto_Repeat_ceval (Original_LF__DOT__Auto_LF_Auto_Repeat_com.CWhile b c) st st''
  | E_RepeatEnd : ∀ st st' b c,
      Original_LF__DOT__Auto_LF_Auto_Repeat_ceval c st st' →
      Original_LF__DOT__Imp_LF_Imp_beval st' b = bool_.true_ →
      Original_LF__DOT__Auto_LF_Auto_Repeat_ceval (Original_LF__DOT__Auto_LF_Auto_Repeat_com.CRepeat c b) st st'
  | E_RepeatLoop : ∀ st st' st'' b c,
      Original_LF__DOT__Auto_LF_Auto_Repeat_ceval c st st' →
      Original_LF__DOT__Imp_LF_Imp_beval st' b = bool_.false_ →
      Original_LF__DOT__Auto_LF_Auto_Repeat_ceval (Original_LF__DOT__Auto_LF_Auto_Repeat_com.CRepeat c b) st' st'' →
      Original_LF__DOT__Auto_LF_Auto_Repeat_ceval (Original_LF__DOT__Auto_LF_Auto_Repeat_com.CRepeat c b) st st''

-- ceval'_example1: The example from the original (Admitted in original, so we use axiom)
-- X := 2; if (X <= 1) then Y := 3 else Z := 4 end
-- Starting from empty_st, ends at (Z !-> 4; X !-> 2)
axiom «Original_LF__DOT__Auto_LF_Auto_ceval'__example1» :
  Original_LF__DOT__Auto_LF_Auto_Repeat_ceval
    (Original_LF__DOT__Auto_LF_Auto_Repeat_com.CSeq
       (Original_LF__DOT__Auto_LF_Auto_Repeat_com.CAsgn Original_LF__DOT__Imp_LF_Imp_X (Original_LF__DOT__Imp_LF_Imp_aexp.ANum (nat_.S_ (nat_.S_ nat_.O_))))
       (Original_LF__DOT__Auto_LF_Auto_Repeat_com.CIf
          (Original_LF__DOT__Imp_LF_Imp_bexp.BLe (Original_LF__DOT__Imp_LF_Imp_aexp.AId Original_LF__DOT__Imp_LF_Imp_X)
             (Original_LF__DOT__Imp_LF_Imp_aexp.ANum (nat_.S_ nat_.O_)))
          (Original_LF__DOT__Auto_LF_Auto_Repeat_com.CAsgn Original_LF__DOT__Imp_LF_Imp_Y (Original_LF__DOT__Imp_LF_Imp_aexp.ANum (nat_.S_ (nat_.S_ (nat_.S_ nat_.O_)))))
          (Original_LF__DOT__Auto_LF_Auto_Repeat_com.CAsgn Original_LF__DOT__Imp_LF_Imp_Z (Original_LF__DOT__Imp_LF_Imp_aexp.ANum (nat_.S_ (nat_.S_ (nat_.S_ (nat_.S_ nat_.O_))))))))
    Original_LF__DOT__Imp_LF_Imp_empty__st
    (Original_LF__DOT__Maps_LF_Maps_t__update
       (Original_LF__DOT__Maps_LF_Maps_t__update Original_LF__DOT__Imp_LF_Imp_empty__st Original_LF__DOT__Imp_LF_Imp_X
          (nat_.S_ (nat_.S_ nat_.O_)))
       Original_LF__DOT__Imp_LF_Imp_Z (nat_.S_ (nat_.S_ (nat_.S_ (nat_.S_ nat_.O_)))))

-- Existential type (ex)
inductive ex {A : Type} (P : A → Prop) : Prop where
  | intro (w : A) (h : P w) : ex P

def ex_intro := @ex.intro

-- eauto_example: exists s', (Y !-> 1 ; X !-> 2) =[ if (X <= Y) then Z := Y - X else Y := X + Z end ]=> s'
-- This is Admitted in the original, so we use axiom
axiom Original_LF__DOT__Auto_LF_Auto_eauto__example :
  ex (fun s' : Original_LF__DOT__Imp_LF_Imp_state =>
    Original_LF__DOT__Auto_LF_Auto_Repeat_ceval
      (Original_LF__DOT__Auto_LF_Auto_Repeat_com.CIf
         (Original_LF__DOT__Imp_LF_Imp_bexp.BLe
            (Original_LF__DOT__Imp_LF_Imp_aexp.AId Original_LF__DOT__Imp_LF_Imp_X)
            (Original_LF__DOT__Imp_LF_Imp_aexp.AId Original_LF__DOT__Imp_LF_Imp_Y))
         (Original_LF__DOT__Auto_LF_Auto_Repeat_com.CAsgn Original_LF__DOT__Imp_LF_Imp_Z
            (Original_LF__DOT__Imp_LF_Imp_aexp.AMinus
               (Original_LF__DOT__Imp_LF_Imp_aexp.AId Original_LF__DOT__Imp_LF_Imp_Y)
               (Original_LF__DOT__Imp_LF_Imp_aexp.AId Original_LF__DOT__Imp_LF_Imp_X)))
         (Original_LF__DOT__Auto_LF_Auto_Repeat_com.CAsgn Original_LF__DOT__Imp_LF_Imp_Y
            (Original_LF__DOT__Imp_LF_Imp_aexp.APlus
               (Original_LF__DOT__Imp_LF_Imp_aexp.AId Original_LF__DOT__Imp_LF_Imp_X)
               (Original_LF__DOT__Imp_LF_Imp_aexp.AId Original_LF__DOT__Imp_LF_Imp_Z))))
      (Original_LF__DOT__Maps_LF_Maps_t__update
         (Original_LF__DOT__Maps_LF_Maps_t__update Original_LF__DOT__Imp_LF_Imp_empty__st Original_LF__DOT__Imp_LF_Imp_X (nat_.S_ (nat_.S_ nat_.O_)))
         Original_LF__DOT__Imp_LF_Imp_Y (nat_.S_ nat_.O_))
      s')

-- ceval_deterministic: determinism of evaluation (Admitted in original, so we use axiom)
-- Use Corelib_Init_Logic_eq to match the expected type in the isomorphism
axiom Original_LF__DOT__Auto_LF_Auto_Repeat_ceval__deterministic :
  ∀ (c : Original_LF__DOT__Auto_LF_Auto_Repeat_com) 
    (st st1 st2 : Original_LF__DOT__Imp_LF_Imp_state),
  Original_LF__DOT__Auto_LF_Auto_Repeat_ceval c st st1 →
  Original_LF__DOT__Auto_LF_Auto_Repeat_ceval c st st2 →
  @Corelib_Init_Logic_eq Original_LF__DOT__Imp_LF_Imp_state st1 st2
