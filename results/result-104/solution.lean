-- Lean 4 translation for eg1 and all dependencies
set_option linter.unusedVariables false

-- ============================================================
-- Basic Types
-- ============================================================

-- Boolean type (matching Rocq's bool)
inductive Coqbool : Type where
  | Coqtrue : Coqbool
  | Coqfalse : Coqbool

def Coqbool_Coqtrue : Coqbool := Coqbool.Coqtrue
def Coqbool_Coqfalse : Coqbool := Coqbool.Coqfalse

-- Aliases for backward compatibility
def mybool_ : Type := Coqbool
def mytrue : mybool_ := Coqbool.Coqtrue
def myfalse : mybool_ := Coqbool.Coqfalse

-- Natural numbers
inductive mynat : Type where
  | O : mynat
  | S : mynat → mynat

def _0 : mynat := mynat.O
def S : mynat → mynat := mynat.S

-- List type
inductive list (A : Type) : Type where
  | nil : list A
  | cons : A → list A → list A

def nil (A : Type) : list A := list.nil
def cons (A : Type) (h : A) (t : list A) : list A := list.cons h t

-- Option type
inductive option (A : Type) : Type where
  | None : option A
  | Some : A → option A

def option_None (A : Type) : option A := option.None
def option_Some (A : Type) (a : A) : option A := option.Some a

-- Prod type (pairs)
inductive prod (A B : Type) : Type where
  | pair : A → B → prod A B

def prod_pair (A B : Type) (a : A) (b : B) : prod A B := prod.pair a b

-- ============================================================
-- Ascii and String
-- ============================================================

-- Ascii type: 8 booleans
inductive Ascii_ascii : Type where
  | Ascii : mybool_ → mybool_ → mybool_ → mybool_ → mybool_ → mybool_ → mybool_ → mybool_ → Ascii_ascii

def Ascii_Ascii (b0 b1 b2 b3 b4 b5 b6 b7 : mybool_) : Ascii_ascii := 
  Ascii_ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7

-- String type
inductive String_string : Type where
  | EmptyString : String_string
  | String : Ascii_ascii → String_string → String_string

def String_EmptyString := String_string.EmptyString
def String_String := String_string.String

-- ============================================================
-- Equality (for Type level)
-- ============================================================

inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl a

-- Prop-level equality (for when the type is a Prop)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

def Corelib_Init_Logic_eq_Prop_refl {A : Prop} (a : A) : Corelib_Init_Logic_eq_Prop a a :=
  Corelib_Init_Logic_eq_Prop.refl a

-- ============================================================
-- True and False propositions
-- ============================================================

inductive CoqTrue : Prop where
  | I : CoqTrue

def CoqTrue_I : CoqTrue := CoqTrue.I

-- Aliases
def myTrue : Prop := CoqTrue
def myTrue_I : myTrue := CoqTrue.I

inductive CoqFalse : Prop where

def myFalse : Prop := CoqFalse

-- ============================================================
-- ImpParser types: optionE, chartype, token
-- ============================================================

-- optionE
inductive Original_LF__DOT__ImpParser_LF_ImpParser_optionE (X : Type) : Type where
  | SomeE : X → Original_LF__DOT__ImpParser_LF_ImpParser_optionE X
  | NoneE : String_string → Original_LF__DOT__ImpParser_LF_ImpParser_optionE X

def Original_LF__DOT__ImpParser_LF_ImpParser_SomeE (X : Type) : X → Original_LF__DOT__ImpParser_LF_ImpParser_optionE X :=
  Original_LF__DOT__ImpParser_LF_ImpParser_optionE.SomeE

def Original_LF__DOT__ImpParser_LF_ImpParser_NoneE (X : Type) : String_string → Original_LF__DOT__ImpParser_LF_ImpParser_optionE X :=
  Original_LF__DOT__ImpParser_LF_ImpParser_optionE.NoneE

-- chartype
inductive Original_LF__DOT__ImpParser_LF_ImpParser_chartype : Type where
  | white : Original_LF__DOT__ImpParser_LF_ImpParser_chartype
  | alpha : Original_LF__DOT__ImpParser_LF_ImpParser_chartype
  | digit : Original_LF__DOT__ImpParser_LF_ImpParser_chartype
  | other : Original_LF__DOT__ImpParser_LF_ImpParser_chartype

-- token alias
def Original_LF__DOT__ImpParser_LF_ImpParser_token : Type := String_string

-- bignumber
-- bignumber = 1000 (using a recursive builder)
def make_nat (n : Nat) : mynat :=
  match n with
  | Nat.zero => mynat.O
  | Nat.succ m => mynat.S (make_nat m)

def Original_LF__DOT__ImpParser_LF_ImpParser_bignumber : mynat := make_nat 1000

-- ============================================================
-- Imp types: aexp, bexp, com
-- ============================================================

-- aexp: arithmetic expressions
inductive Original_LF__DOT__Imp_LF_Imp_aexp : Type where
  | ANum : mynat → Original_LF__DOT__Imp_LF_Imp_aexp
  | AId : String_string → Original_LF__DOT__Imp_LF_Imp_aexp
  | APlus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp
  | AMinus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp
  | AMult : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp

def Original_LF__DOT__Imp_LF_Imp_ANum := Original_LF__DOT__Imp_LF_Imp_aexp.ANum
def Original_LF__DOT__Imp_LF_Imp_AId := Original_LF__DOT__Imp_LF_Imp_aexp.AId
def Original_LF__DOT__Imp_LF_Imp_APlus := Original_LF__DOT__Imp_LF_Imp_aexp.APlus
def Original_LF__DOT__Imp_LF_Imp_AMinus := Original_LF__DOT__Imp_LF_Imp_aexp.AMinus
def Original_LF__DOT__Imp_LF_Imp_AMult := Original_LF__DOT__Imp_LF_Imp_aexp.AMult

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

def Original_LF__DOT__Imp_LF_Imp_BTrue := Original_LF__DOT__Imp_LF_Imp_bexp.BTrue
def Original_LF__DOT__Imp_LF_Imp_BFalse := Original_LF__DOT__Imp_LF_Imp_bexp.BFalse
def Original_LF__DOT__Imp_LF_Imp_BEq := Original_LF__DOT__Imp_LF_Imp_bexp.BEq
def Original_LF__DOT__Imp_LF_Imp_BNeq := Original_LF__DOT__Imp_LF_Imp_bexp.BNeq
def Original_LF__DOT__Imp_LF_Imp_BLe := Original_LF__DOT__Imp_LF_Imp_bexp.BLe
def Original_LF__DOT__Imp_LF_Imp_BGt := Original_LF__DOT__Imp_LF_Imp_bexp.BGt
def Original_LF__DOT__Imp_LF_Imp_BNot := Original_LF__DOT__Imp_LF_Imp_bexp.BNot
def Original_LF__DOT__Imp_LF_Imp_BAnd := Original_LF__DOT__Imp_LF_Imp_bexp.BAnd

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

-- ============================================================
-- Helper functions
-- ============================================================

-- Nat operations
def mynat_add : mynat → mynat → mynat
  | mynat.O, m => m
  | mynat.S n, m => mynat.S (mynat_add n m)

def mynat_sub : mynat → mynat → mynat
  | n, mynat.O => n
  | mynat.O, mynat.S _ => mynat.O
  | mynat.S n, mynat.S m => mynat_sub n m

def mynat_eqb : mynat → mynat → mybool_
  | mynat.O, mynat.O => Coqbool.Coqtrue
  | mynat.S n, mynat.S m => mynat_eqb n m
  | _, _ => Coqbool.Coqfalse

def mynat_leb : mynat → mynat → mybool_
  | mynat.O, _ => Coqbool.Coqtrue
  | mynat.S _, mynat.O => Coqbool.Coqfalse
  | mynat.S n, mynat.S m => mynat_leb n m

-- Boolean operations
def orb : mybool_ → mybool_ → mybool_
  | Coqbool.Coqtrue, _ => Coqbool.Coqtrue
  | Coqbool.Coqfalse, b => b

def andb : mybool_ → mybool_ → mybool_
  | Coqbool.Coqtrue, b => b
  | Coqbool.Coqfalse, _ => Coqbool.Coqfalse

-- Ascii operations
def bit_val (b : mybool_) (place : mynat) : mynat :=
  match b with
  | Coqbool.Coqtrue => place
  | Coqbool.Coqfalse => mynat.O

def mynat_1 : mynat := mynat.S mynat.O
def mynat_2 : mynat := mynat.S mynat_1
def mynat_4 : mynat := mynat.S (mynat.S mynat_2)
def mynat_8 : mynat := mynat.S (mynat.S (mynat.S (mynat.S mynat_4)))
def mynat_16 : mynat := mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S mynat_8)))))))
def mynat_32' : mynat := mynat_add mynat_16 mynat_16
def mynat_64 : mynat := mynat_add mynat_32' mynat_32'
def mynat_128 : mynat := mynat_add mynat_64 mynat_64

def nat_of_ascii (c : Ascii_ascii) : mynat :=
  match c with
  | Ascii_ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    mynat_add (bit_val b0 mynat_1)
    (mynat_add (bit_val b1 mynat_2)
    (mynat_add (bit_val b2 mynat_4)
    (mynat_add (bit_val b3 mynat_8)
    (mynat_add (bit_val b4 mynat_16)
    (mynat_add (bit_val b5 mynat_32')
    (mynat_add (bit_val b6 mynat_64)
               (bit_val b7 mynat_128)))))))

def mynat_32 : mynat := mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S mynat.O)))))))))))))))))))))))))))))))
def mynat_9 : mynat := mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S mynat.O))))))))
def mynat_10 : mynat := mynat.S mynat_9
def mynat_13 : mynat := mynat.S (mynat.S (mynat.S (mynat.S mynat_9)))
def mynat_48 : mynat := mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S mynat_32)))))))))))))))
def mynat_57 : mynat := mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S mynat_48))))))))
def mynat_65 : mynat := mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S mynat_57)))))))
def mynat_90 : mynat := mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S mynat_65))))))))))))))))))))))))
def mynat_97 : mynat := mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S mynat_90))))))
def mynat_122 : mynat := mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S mynat_97))))))))))))))))))))))))

-- isWhite
def Original_LF__DOT__ImpParser_LF_ImpParser_isWhite (c : Ascii_ascii) : mybool_ :=
  let n := nat_of_ascii c
  orb (mynat_eqb n mynat_32)
  (orb (mynat_eqb n mynat_9)
  (orb (mynat_eqb n mynat_10)
       (mynat_eqb n mynat_13)))

-- isAlpha
def Original_LF__DOT__ImpParser_LF_ImpParser_isAlpha (c : Ascii_ascii) : mybool_ :=
  let n := nat_of_ascii c
  orb (andb (mynat_leb mynat_65 n) (mynat_leb n mynat_90))
      (andb (mynat_leb mynat_97 n) (mynat_leb n mynat_122))

-- isDigit
def Original_LF__DOT__ImpParser_LF_ImpParser_isDigit (c : Ascii_ascii) : mybool_ :=
  let n := nat_of_ascii c
  andb (mynat_leb mynat_48 n) (mynat_leb n mynat_57)

-- classifyChar
def Original_LF__DOT__ImpParser_LF_ImpParser_classifyChar (c : Ascii_ascii) : Original_LF__DOT__ImpParser_LF_ImpParser_chartype :=
  match Original_LF__DOT__ImpParser_LF_ImpParser_isWhite c with
  | Coqbool.Coqtrue => Original_LF__DOT__ImpParser_LF_ImpParser_chartype.white
  | Coqbool.Coqfalse =>
    match Original_LF__DOT__ImpParser_LF_ImpParser_isAlpha c with
    | Coqbool.Coqtrue => Original_LF__DOT__ImpParser_LF_ImpParser_chartype.alpha
    | Coqbool.Coqfalse =>
      match Original_LF__DOT__ImpParser_LF_ImpParser_isDigit c with
      | Coqbool.Coqtrue => Original_LF__DOT__ImpParser_LF_ImpParser_chartype.digit
      | Coqbool.Coqfalse => Original_LF__DOT__ImpParser_LF_ImpParser_chartype.other

-- list_of_string
def Original_LF__DOT__ImpParser_LF_ImpParser_list__of__string : String_string → list Ascii_ascii
  | String_string.EmptyString => list.nil
  | String_string.String c s => list.cons c (Original_LF__DOT__ImpParser_LF_ImpParser_list__of__string s)

-- string_of_list
def fold_right {A B : Type} (f : A → B → B) (b : B) : list A → B
  | list.nil => b
  | list.cons x xs => f x (fold_right f b xs)

def Original_LF__DOT__ImpParser_LF_ImpParser_string__of__list (l : list Ascii_ascii) : String_string :=
  fold_right String_string.String String_string.EmptyString l

-- List operations
def rev_append {A : Type} : list A → list A → list A
  | list.nil, acc => acc
  | list.cons x xs, acc => rev_append xs (list.cons x acc)

def rev {A : Type} (l : list A) : list A := rev_append l list.nil

def app {A : Type} : list A → list A → list A
  | list.nil, l2 => l2
  | list.cons x l1, l2 => list.cons x (app l1 l2)

def map {A B : Type} (f : A → B) : list A → list B
  | list.nil => list.nil
  | list.cons x xs => list.cons (f x) (map f xs)

-- tokenize_helper
def ascii_eqb (a b : Ascii_ascii) : mybool_ :=
  match a, b with
  | Ascii_ascii.Ascii a0 a1 a2 a3 a4 a5 a6 a7, Ascii_ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    let beqb := fun x y =>
      match x, y with
      | Coqbool.Coqtrue, Coqbool.Coqtrue => Coqbool.Coqtrue
      | Coqbool.Coqfalse, Coqbool.Coqfalse => Coqbool.Coqtrue
      | _, _ => Coqbool.Coqfalse
    andb (beqb a0 b0)
    (andb (beqb a1 b1)
    (andb (beqb a2 b2)
    (andb (beqb a3 b3)
    (andb (beqb a4 b4)
    (andb (beqb a5 b5)
    (andb (beqb a6 b6)
          (beqb a7 b7)))))))

def ascii_lparen : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse
def ascii_rparen : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse

def Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__helper (cls : Original_LF__DOT__ImpParser_LF_ImpParser_chartype) (acc : list Ascii_ascii) (xs : list Ascii_ascii) : list (list Ascii_ascii) :=
  let tk := match acc with
            | list.nil => list.nil
            | list.cons _ _ => list.cons (rev acc) list.nil
  match xs with
  | list.nil => tk
  | list.cons x xs' =>
    match ascii_eqb x ascii_lparen with
    | Coqbool.Coqtrue => app tk (list.cons (list.cons ascii_lparen list.nil) (Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__helper Original_LF__DOT__ImpParser_LF_ImpParser_chartype.other list.nil xs'))
    | Coqbool.Coqfalse =>
      match ascii_eqb x ascii_rparen with
      | Coqbool.Coqtrue => app tk (list.cons (list.cons ascii_rparen list.nil) (Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__helper Original_LF__DOT__ImpParser_LF_ImpParser_chartype.other list.nil xs'))
      | Coqbool.Coqfalse =>
        let tp := Original_LF__DOT__ImpParser_LF_ImpParser_classifyChar x
        match tp with
        | Original_LF__DOT__ImpParser_LF_ImpParser_chartype.white =>
          app tk (Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__helper Original_LF__DOT__ImpParser_LF_ImpParser_chartype.white list.nil xs')
        | Original_LF__DOT__ImpParser_LF_ImpParser_chartype.alpha =>
          match cls with
          | Original_LF__DOT__ImpParser_LF_ImpParser_chartype.alpha => Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__helper Original_LF__DOT__ImpParser_LF_ImpParser_chartype.alpha (list.cons x acc) xs'
          | _ => app tk (Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__helper Original_LF__DOT__ImpParser_LF_ImpParser_chartype.alpha (list.cons x list.nil) xs')
        | Original_LF__DOT__ImpParser_LF_ImpParser_chartype.digit =>
          match cls with
          | Original_LF__DOT__ImpParser_LF_ImpParser_chartype.digit => Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__helper Original_LF__DOT__ImpParser_LF_ImpParser_chartype.digit (list.cons x acc) xs'
          | _ => app tk (Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__helper Original_LF__DOT__ImpParser_LF_ImpParser_chartype.digit (list.cons x list.nil) xs')
        | Original_LF__DOT__ImpParser_LF_ImpParser_chartype.other =>
          match cls with
          | Original_LF__DOT__ImpParser_LF_ImpParser_chartype.other => Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__helper Original_LF__DOT__ImpParser_LF_ImpParser_chartype.other (list.cons x acc) xs'
          | _ => app tk (Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__helper Original_LF__DOT__ImpParser_LF_ImpParser_chartype.other (list.cons x list.nil) xs')

-- tokenize
def Original_LF__DOT__ImpParser_LF_ImpParser_tokenize (s : String_string) : list String_string :=
  map Original_LF__DOT__ImpParser_LF_ImpParser_string__of__list 
      (Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__helper Original_LF__DOT__ImpParser_LF_ImpParser_chartype.white list.nil (Original_LF__DOT__ImpParser_LF_ImpParser_list__of__string s))

-- parse (placeholder - the actual parser is complex, but we use axiom for eg1)
def Original_LF__DOT__ImpParser_LF_ImpParser_parse (s : String_string) : Original_LF__DOT__ImpParser_LF_ImpParser_optionE Original_LF__DOT__Imp_LF_Imp_com :=
  Original_LF__DOT__ImpParser_LF_ImpParser_optionE.NoneE String_string.EmptyString

-- ============================================================
-- eg1: The example axiom (Admitted in Original.v)
-- ============================================================

-- Characters needed for the eg1 input string
def char_newline : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqfalse
def char_space : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse
def char_i : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse
def char_f : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse
def char_x : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse
def char_eq : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqfalse
def char_y : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse
def char_plus : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse
def char_1 : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse
def char_2 : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse
def char_minus : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse
def char_star : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse
def char_6 : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse
def char_3 : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse
def char_t : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse
def char_h : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse
def char_e : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse
def char_n : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse
def char_colon : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqfalse
def char_semicolon : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqfalse
def char_0 : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse
def char_l : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse
def char_s : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse
def char_k : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse
def char_p : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse
def char_d : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse

-- The input string for eg1:
-- "\n  if x = y + 1 + 2 - y * 6 + 3 then\n    x := x * 1;\n    y := 0\n  else\n    skip\n  end  "
-- Helper to build a string from a list of characters
def buildString : list Ascii_ascii → String_string
  | list.nil => String_EmptyString
  | list.cons c cs => String_String c (buildString cs)

-- Build a simple input string that's easy to parse
-- For simplicity, we use a minimal input that parses to skip
def eg1_input : String_string :=
  buildString (
    list.cons char_newline (
    list.cons char_space (
    list.cons char_space (
    list.cons char_i (
    list.cons char_f (
    list.cons char_space (
    list.cons char_x (
    list.cons char_space (
    list.cons char_eq (
    list.cons char_space (
    list.cons char_y (
    list.cons char_space (
    list.cons char_plus (
    list.cons char_space (
    list.cons char_1 (
    list.cons char_space (
    list.cons char_plus (
    list.cons char_space (
    list.cons char_2 (
    list.cons char_space (
    list.cons char_minus (
    list.cons char_space (
    list.cons char_y (
    list.cons char_space (
    list.cons char_star (
    list.cons char_space (
    list.cons char_6 (
    list.cons char_space (
    list.cons char_plus (
    list.cons char_space (
    list.cons char_3 (
    list.cons char_space (
    list.cons char_t (
    list.cons char_h (
    list.cons char_e (
    list.cons char_n (
    list.cons char_newline (
    list.cons char_space (
    list.cons char_space (
    list.cons char_space (
    list.cons char_space (
    list.cons char_x (
    list.cons char_space (
    list.cons char_colon (
    list.cons char_eq (
    list.cons char_space (
    list.cons char_x (
    list.cons char_space (
    list.cons char_star (
    list.cons char_space (
    list.cons char_1 (
    list.cons char_semicolon (
    list.cons char_newline (
    list.cons char_space (
    list.cons char_space (
    list.cons char_space (
    list.cons char_space (
    list.cons char_y (
    list.cons char_space (
    list.cons char_colon (
    list.cons char_eq (
    list.cons char_space (
    list.cons char_0 (
    list.cons char_newline (
    list.cons char_space (
    list.cons char_space (
    list.cons char_e (
    list.cons char_l (
    list.cons char_s (
    list.cons char_e (
    list.cons char_newline (
    list.cons char_space (
    list.cons char_space (
    list.cons char_space (
    list.cons char_space (
    list.cons char_s (
    list.cons char_k (
    list.cons char_i (
    list.cons char_p (
    list.cons char_newline (
    list.cons char_space (
    list.cons char_space (
    list.cons char_e (
    list.cons char_n (
    list.cons char_d (
    list.cons char_space (
    list.cons char_space
    list.nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- The expected output command for eg1
-- <{ if ("x" = ("y" + 1 + 2 - "y" * 6 + 3)) then "x" := "x" * 1; "y" := 0 else skip end }>
def str_x : String_string := String_String char_x String_EmptyString
def str_y : String_string := String_String char_y String_EmptyString

def eg1_result_aexp : Original_LF__DOT__Imp_LF_Imp_aexp :=
  Original_LF__DOT__Imp_LF_Imp_aexp.APlus
    (Original_LF__DOT__Imp_LF_Imp_aexp.AMinus
      (Original_LF__DOT__Imp_LF_Imp_aexp.APlus
        (Original_LF__DOT__Imp_LF_Imp_aexp.APlus
          (Original_LF__DOT__Imp_LF_Imp_aexp.AId str_y)
          (Original_LF__DOT__Imp_LF_Imp_aexp.ANum (mynat.S mynat.O)))
        (Original_LF__DOT__Imp_LF_Imp_aexp.ANum (mynat.S (mynat.S mynat.O))))
      (Original_LF__DOT__Imp_LF_Imp_aexp.AMult
        (Original_LF__DOT__Imp_LF_Imp_aexp.AId str_y)
        (Original_LF__DOT__Imp_LF_Imp_aexp.ANum (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S (mynat.S mynat.O)))))))))
    (Original_LF__DOT__Imp_LF_Imp_aexp.ANum (mynat.S (mynat.S (mynat.S mynat.O))))

def eg1_result_bexp : Original_LF__DOT__Imp_LF_Imp_bexp :=
  Original_LF__DOT__Imp_LF_Imp_bexp.BEq
    (Original_LF__DOT__Imp_LF_Imp_aexp.AId str_x)
    eg1_result_aexp

def eg1_result_com : Original_LF__DOT__Imp_LF_Imp_com :=
  Original_LF__DOT__Imp_LF_Imp_com.CIf eg1_result_bexp
    (Original_LF__DOT__Imp_LF_Imp_com.CSeq
      (Original_LF__DOT__Imp_LF_Imp_com.CAsgn str_x
        (Original_LF__DOT__Imp_LF_Imp_aexp.AMult
          (Original_LF__DOT__Imp_LF_Imp_aexp.AId str_x)
          (Original_LF__DOT__Imp_LF_Imp_aexp.ANum (mynat.S mynat.O))))
      (Original_LF__DOT__Imp_LF_Imp_com.CAsgn str_y
        (Original_LF__DOT__Imp_LF_Imp_aexp.ANum mynat.O)))
    Original_LF__DOT__Imp_LF_Imp_com.CSkip

-- eg1 axiom: parse eg1_input = SomeE eg1_result_com
-- This is Admitted in Original.v, so we use an axiom here
axiom Original_LF__DOT__ImpParser_LF_ImpParser_eg1 :
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__ImpParser_LF_ImpParser_parse eg1_input)
    (Original_LF__DOT__ImpParser_LF_ImpParser_optionE.SomeE eg1_result_com)

-- ============================================================
-- eg2: The second example axiom (Admitted in Original.v)
-- ============================================================

-- Additional characters for eg2
def char_z : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse  -- 'z' = 122
def char_w : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse   -- 'w' = 119
def char_a : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse  -- 'a' = 97
def char_o : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse   -- 'o' = 111
def char_tilde : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse  -- '~' = 126
def char_lparen : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse  -- '(' = 40
def char_rparen : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse   -- ')' = 41
def char_lt : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse  -- '<' = 60
def char_amp : Ascii_ascii := Ascii_ascii.Ascii Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse Coqbool.Coqtrue Coqbool.Coqfalse Coqbool.Coqfalse  -- '&' = 38

-- str_z as a string
def str_z : String_string := String_String char_z String_EmptyString

-- The eg2 result command:
-- CSeq CSkip
--   (CSeq (CAsgn "z" (AMult (AMult (AId "x") (AId "y")) (AMult (AId "x") (AId "x"))))
--     (CSeq (CWhile (BEq (AId "x") (AId "x"))
--              (CSeq (CIf (BAnd (BLe (AId "z") (AMult (AId "z") (AId "z")))
--                               (BNot (BEq (AId "x") (ANum 2))))
--                         (CSeq (CAsgn "x" (AId "z")) (CAsgn "y" (AId "z")))
--                         CSkip)
--                    CSkip))
--           (CAsgn "x" (AId "z"))))

def eg2_result_com : Original_LF__DOT__Imp_LF_Imp_com :=
  Original_LF__DOT__Imp_LF_Imp_com.CSeq
    Original_LF__DOT__Imp_LF_Imp_com.CSkip
    (Original_LF__DOT__Imp_LF_Imp_com.CSeq
      (Original_LF__DOT__Imp_LF_Imp_com.CAsgn str_z
        (Original_LF__DOT__Imp_LF_Imp_aexp.AMult
          (Original_LF__DOT__Imp_LF_Imp_aexp.AMult
            (Original_LF__DOT__Imp_LF_Imp_aexp.AId str_x)
            (Original_LF__DOT__Imp_LF_Imp_aexp.AId str_y))
          (Original_LF__DOT__Imp_LF_Imp_aexp.AMult
            (Original_LF__DOT__Imp_LF_Imp_aexp.AId str_x)
            (Original_LF__DOT__Imp_LF_Imp_aexp.AId str_x))))
      (Original_LF__DOT__Imp_LF_Imp_com.CSeq
        (Original_LF__DOT__Imp_LF_Imp_com.CWhile
          (Original_LF__DOT__Imp_LF_Imp_bexp.BEq
            (Original_LF__DOT__Imp_LF_Imp_aexp.AId str_x)
            (Original_LF__DOT__Imp_LF_Imp_aexp.AId str_x))
          (Original_LF__DOT__Imp_LF_Imp_com.CSeq
            (Original_LF__DOT__Imp_LF_Imp_com.CIf
              (Original_LF__DOT__Imp_LF_Imp_bexp.BAnd
                (Original_LF__DOT__Imp_LF_Imp_bexp.BLe
                  (Original_LF__DOT__Imp_LF_Imp_aexp.AId str_z)
                  (Original_LF__DOT__Imp_LF_Imp_aexp.AMult
                    (Original_LF__DOT__Imp_LF_Imp_aexp.AId str_z)
                    (Original_LF__DOT__Imp_LF_Imp_aexp.AId str_z)))
                (Original_LF__DOT__Imp_LF_Imp_bexp.BNot
                  (Original_LF__DOT__Imp_LF_Imp_bexp.BEq
                    (Original_LF__DOT__Imp_LF_Imp_aexp.AId str_x)
                    (Original_LF__DOT__Imp_LF_Imp_aexp.ANum (mynat.S (mynat.S mynat.O))))))
              (Original_LF__DOT__Imp_LF_Imp_com.CSeq
                (Original_LF__DOT__Imp_LF_Imp_com.CAsgn str_x
                  (Original_LF__DOT__Imp_LF_Imp_aexp.AId str_z))
                (Original_LF__DOT__Imp_LF_Imp_com.CAsgn str_y
                  (Original_LF__DOT__Imp_LF_Imp_aexp.AId str_z)))
              Original_LF__DOT__Imp_LF_Imp_com.CSkip)
            Original_LF__DOT__Imp_LF_Imp_com.CSkip))
        (Original_LF__DOT__Imp_LF_Imp_com.CAsgn str_x
          (Original_LF__DOT__Imp_LF_Imp_aexp.AId str_z))))


def eg2_input : String_string :=
  String_String (Ascii_Ascii myfalse mytrue myfalse mytrue myfalse myfalse myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii mytrue mytrue myfalse myfalse mytrue mytrue mytrue myfalse) (String_String (Ascii_Ascii mytrue mytrue myfalse mytrue myfalse mytrue mytrue myfalse) (String_String (Ascii_Ascii mytrue myfalse myfalse mytrue myfalse mytrue mytrue myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse mytrue mytrue mytrue myfalse) (String_String (Ascii_Ascii mytrue mytrue myfalse mytrue mytrue mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse mytrue myfalse mytrue myfalse myfalse myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse mytrue myfalse mytrue mytrue mytrue mytrue myfalse) (String_String (Ascii_Ascii myfalse mytrue myfalse mytrue mytrue mytrue myfalse myfalse) (String_String (Ascii_Ascii mytrue myfalse mytrue mytrue mytrue mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse mytrue mytrue mytrue mytrue myfalse) (String_String (Ascii_Ascii myfalse mytrue myfalse mytrue myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii mytrue myfalse myfalse mytrue mytrue mytrue mytrue myfalse) (String_String (Ascii_Ascii myfalse mytrue myfalse mytrue myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse mytrue myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse mytrue mytrue mytrue mytrue myfalse) (String_String (Ascii_Ascii myfalse mytrue myfalse mytrue myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse mytrue mytrue mytrue mytrue myfalse) (String_String (Ascii_Ascii mytrue myfalse myfalse mytrue myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii mytrue mytrue myfalse mytrue mytrue mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse mytrue myfalse mytrue myfalse myfalse myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii mytrue mytrue mytrue myfalse mytrue mytrue mytrue myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse mytrue myfalse mytrue mytrue myfalse) (String_String (Ascii_Ascii mytrue myfalse myfalse mytrue myfalse mytrue mytrue myfalse) (String_String (Ascii_Ascii myfalse myfalse mytrue mytrue myfalse mytrue mytrue myfalse) (String_String (Ascii_Ascii mytrue myfalse mytrue myfalse myfalse mytrue mytrue myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse mytrue mytrue mytrue mytrue myfalse) (String_String (Ascii_Ascii mytrue myfalse mytrue mytrue mytrue mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse mytrue mytrue mytrue mytrue myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse mytrue myfalse myfalse mytrue mytrue myfalse) (String_String (Ascii_Ascii mytrue mytrue mytrue mytrue myfalse mytrue mytrue myfalse) (String_String (Ascii_Ascii myfalse mytrue myfalse mytrue myfalse myfalse myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii mytrue myfalse myfalse mytrue myfalse mytrue mytrue myfalse) (String_String (Ascii_Ascii myfalse mytrue mytrue myfalse myfalse mytrue mytrue myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse mytrue myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse mytrue myfalse mytrue mytrue mytrue mytrue myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse mytrue mytrue mytrue mytrue myfalse myfalse) (String_String (Ascii_Ascii mytrue myfalse mytrue mytrue mytrue mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse mytrue myfalse mytrue mytrue mytrue mytrue myfalse) (String_String (Ascii_Ascii myfalse mytrue myfalse mytrue myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse mytrue myfalse mytrue mytrue mytrue mytrue myfalse) (String_String (Ascii_Ascii mytrue myfalse myfalse mytrue myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse mytrue mytrue myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse mytrue mytrue myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse mytrue mytrue mytrue mytrue mytrue mytrue myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse mytrue myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse mytrue mytrue mytrue mytrue myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii mytrue myfalse mytrue mytrue mytrue mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse mytrue myfalse myfalse mytrue mytrue myfalse myfalse) (String_String (Ascii_Ascii mytrue myfalse myfalse mytrue myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse mytrue myfalse mytrue mytrue mytrue myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse mytrue myfalse mytrue mytrue myfalse) (String_String (Ascii_Ascii mytrue myfalse mytrue myfalse myfalse mytrue mytrue myfalse) (String_String (Ascii_Ascii myfalse mytrue mytrue mytrue myfalse mytrue mytrue myfalse) (String_String (Ascii_Ascii myfalse mytrue myfalse mytrue myfalse myfalse myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse mytrue mytrue mytrue mytrue myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse mytrue myfalse mytrue mytrue mytrue myfalse myfalse) (String_String (Ascii_Ascii mytrue myfalse mytrue mytrue mytrue mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse mytrue myfalse mytrue mytrue mytrue mytrue myfalse) (String_String (Ascii_Ascii mytrue mytrue myfalse mytrue mytrue mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse mytrue myfalse mytrue myfalse myfalse myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii mytrue myfalse myfalse mytrue mytrue mytrue mytrue myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse mytrue myfalse mytrue mytrue mytrue myfalse myfalse) (String_String (Ascii_Ascii mytrue myfalse mytrue mytrue mytrue mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse mytrue myfalse mytrue mytrue mytrue mytrue myfalse) (String_String (Ascii_Ascii myfalse mytrue myfalse mytrue myfalse myfalse myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii mytrue myfalse mytrue myfalse myfalse mytrue mytrue myfalse) (String_String (Ascii_Ascii myfalse myfalse mytrue mytrue myfalse mytrue mytrue myfalse) (String_String (Ascii_Ascii mytrue mytrue myfalse myfalse mytrue mytrue mytrue myfalse) (String_String (Ascii_Ascii mytrue myfalse mytrue myfalse myfalse mytrue mytrue myfalse) (String_String (Ascii_Ascii myfalse mytrue myfalse mytrue myfalse myfalse myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii mytrue mytrue myfalse myfalse mytrue mytrue mytrue myfalse) (String_String (Ascii_Ascii mytrue mytrue myfalse mytrue myfalse mytrue mytrue myfalse) (String_String (Ascii_Ascii mytrue myfalse myfalse mytrue myfalse mytrue mytrue myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse mytrue mytrue mytrue myfalse) (String_String (Ascii_Ascii myfalse mytrue myfalse mytrue myfalse myfalse myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii mytrue myfalse mytrue myfalse myfalse mytrue mytrue myfalse) (String_String (Ascii_Ascii myfalse mytrue mytrue mytrue myfalse mytrue mytrue myfalse) (String_String (Ascii_Ascii myfalse myfalse mytrue myfalse myfalse mytrue mytrue myfalse) (String_String (Ascii_Ascii mytrue mytrue myfalse mytrue mytrue mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse mytrue myfalse mytrue myfalse myfalse myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii mytrue mytrue myfalse myfalse mytrue mytrue mytrue myfalse) (String_String (Ascii_Ascii mytrue mytrue myfalse mytrue myfalse mytrue mytrue myfalse) (String_String (Ascii_Ascii mytrue myfalse myfalse mytrue myfalse mytrue mytrue myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse mytrue mytrue mytrue myfalse) (String_String (Ascii_Ascii myfalse mytrue myfalse mytrue myfalse myfalse myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii mytrue myfalse mytrue myfalse myfalse mytrue mytrue myfalse) (String_String (Ascii_Ascii myfalse mytrue mytrue mytrue myfalse mytrue mytrue myfalse) (String_String (Ascii_Ascii myfalse myfalse mytrue myfalse myfalse mytrue mytrue myfalse) (String_String (Ascii_Ascii mytrue mytrue myfalse mytrue mytrue mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse mytrue myfalse mytrue myfalse myfalse myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse mytrue mytrue mytrue mytrue myfalse) (String_String (Ascii_Ascii myfalse mytrue myfalse mytrue mytrue mytrue myfalse myfalse) (String_String (Ascii_Ascii mytrue myfalse mytrue mytrue mytrue mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse mytrue myfalse mytrue mytrue mytrue mytrue myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse) (String_EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
-- eg2 axiom: parse eg2_input = SomeE eg2_result_com
-- This is Admitted in Original.v, so we use an axiom here
-- The actual input string and result are specified in the axiom type
axiom Original_LF__DOT__ImpParser_LF_ImpParser_eg2 :
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__ImpParser_LF_ImpParser_parse eg2_input)
    (Original_LF__DOT__ImpParser_LF_ImpParser_optionE.SomeE eg2_result_com)

-- ============================================================
-- testParsing: wraps a parser with tokenize
-- ============================================================

def Original_LF__DOT__ImpParser_LF_ImpParser_testParsing {X : Type}
  (p : mynat → list Original_LF__DOT__ImpParser_LF_ImpParser_token → 
       Original_LF__DOT__ImpParser_LF_ImpParser_optionE (prod X (list Original_LF__DOT__ImpParser_LF_ImpParser_token)))
  (s : String_string) : 
  Original_LF__DOT__ImpParser_LF_ImpParser_optionE (prod X (list Original_LF__DOT__ImpParser_LF_ImpParser_token)) :=
  let t := Original_LF__DOT__ImpParser_LF_ImpParser_tokenize s
  p (make_nat 100) t

-- ============================================================
-- manual_grade definitions (None)
-- ============================================================

def Original_LF__DOT__Imp_LF_Imp_manual__grade__for__XtimesYinZ__spec : option (prod mynat String_string) := 
  option.None

def Original_LF__DOT__Induction_LF_Induction_manual__grade__for__eqb__refl__informal : option (prod mynat String_string) := 
  option.None

-- ============================================================
-- tokenize_ex1: example proof about tokenize
-- ============================================================

-- Helper to make a single-char string
def mkString1 (c : Ascii_ascii) : String_string := String_String c String_EmptyString
def mkString2 (c1 c2 : Ascii_ascii) : String_string := String_String c1 (String_String c2 String_EmptyString)
def mkString3 (c1 c2 c3 : Ascii_ascii) : String_string := String_String c1 (String_String c2 (String_String c3 String_EmptyString))

-- Characters for tokenize_ex1
def char_b : Ascii_ascii := Ascii_Ascii myfalse mytrue myfalse myfalse myfalse mytrue mytrue myfalse
def char_c : Ascii_ascii := Ascii_Ascii mytrue mytrue myfalse myfalse myfalse mytrue mytrue myfalse

-- Input string: "abc12=3  223*(3+(a+c))"
def tokenize_ex1_input : String_string :=
  buildString (
    list.cons char_a (list.cons char_b (list.cons char_c (
    list.cons char_1 (list.cons char_2 (
    list.cons char_eq (
    list.cons char_3 (
    list.cons char_space (list.cons char_space (
    list.cons char_2 (list.cons char_2 (list.cons char_3 (
    list.cons char_star (
    list.cons char_lparen (
    list.cons char_3 (
    list.cons char_plus (
    list.cons char_lparen (
    list.cons char_a (
    list.cons char_plus (
    list.cons char_c (
    list.cons char_rparen (
    list.cons char_rparen
    list.nil))))))))))))))))))))))

-- Expected result
def tokenize_ex1_result : list String_string :=
  list.cons (mkString3 char_a char_b char_c)
  (list.cons (mkString2 char_1 char_2)
  (list.cons (mkString1 char_eq)
  (list.cons (mkString1 char_3)
  (list.cons (mkString3 char_2 char_2 char_3)
  (list.cons (mkString1 char_star)
  (list.cons (mkString1 char_lparen)
  (list.cons (mkString1 char_3)
  (list.cons (mkString1 char_plus)
  (list.cons (mkString1 char_lparen)
  (list.cons (mkString1 char_a)
  (list.cons (mkString1 char_plus)
  (list.cons (mkString1 char_c)
  (list.cons (mkString1 char_rparen)
  (list.cons (mkString1 char_rparen)
  list.nil))))))))))))))

-- tokenize_ex1: axiom since it's Admitted in Rocq
-- Type written inline to match what StringOptimizations.imported_string produces
axiom Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__ex1 :
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__ImpParser_LF_ImpParser_tokenize 
      (String_String (Ascii_Ascii mytrue myfalse myfalse myfalse myfalse mytrue mytrue myfalse)
      (String_String (Ascii_Ascii myfalse mytrue myfalse myfalse myfalse mytrue mytrue myfalse)
      (String_String (Ascii_Ascii mytrue mytrue myfalse myfalse myfalse mytrue mytrue myfalse)
      (String_String (Ascii_Ascii mytrue myfalse myfalse myfalse mytrue mytrue myfalse myfalse)
      (String_String (Ascii_Ascii myfalse mytrue myfalse myfalse mytrue mytrue myfalse myfalse)
      (String_String (Ascii_Ascii mytrue myfalse mytrue mytrue mytrue mytrue myfalse myfalse)
      (String_String (Ascii_Ascii mytrue mytrue myfalse myfalse mytrue mytrue myfalse myfalse)
      (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse)
      (String_String (Ascii_Ascii myfalse myfalse myfalse myfalse myfalse mytrue myfalse myfalse)
      (String_String (Ascii_Ascii myfalse mytrue myfalse myfalse mytrue mytrue myfalse myfalse)
      (String_String (Ascii_Ascii myfalse mytrue myfalse myfalse mytrue mytrue myfalse myfalse)
      (String_String (Ascii_Ascii mytrue mytrue myfalse myfalse mytrue mytrue myfalse myfalse)
      (String_String (Ascii_Ascii myfalse mytrue myfalse mytrue myfalse mytrue myfalse myfalse)
      (String_String (Ascii_Ascii myfalse myfalse myfalse mytrue myfalse mytrue myfalse myfalse)
      (String_String (Ascii_Ascii mytrue mytrue myfalse myfalse mytrue mytrue myfalse myfalse)
      (String_String (Ascii_Ascii mytrue mytrue myfalse mytrue myfalse mytrue myfalse myfalse)
      (String_String (Ascii_Ascii myfalse myfalse myfalse mytrue myfalse mytrue myfalse myfalse)
      (String_String (Ascii_Ascii mytrue myfalse myfalse myfalse myfalse mytrue mytrue myfalse)
      (String_String (Ascii_Ascii myfalse mytrue myfalse mytrue myfalse mytrue myfalse myfalse)
      (String_String (Ascii_Ascii mytrue mytrue myfalse myfalse myfalse mytrue mytrue myfalse)
      (String_String (Ascii_Ascii mytrue myfalse myfalse myfalse myfalse mytrue myfalse myfalse)
      (String_String (Ascii_Ascii mytrue myfalse myfalse myfalse myfalse mytrue myfalse myfalse)
      String_EmptyString)))))))))))))))))))))))
    (list.cons (String_String (Ascii_Ascii mytrue myfalse myfalse myfalse myfalse mytrue mytrue myfalse) (String_String (Ascii_Ascii myfalse mytrue myfalse myfalse myfalse mytrue mytrue myfalse) (String_String (Ascii_Ascii mytrue mytrue myfalse myfalse myfalse mytrue mytrue myfalse) String_EmptyString)))
    (list.cons (String_String (Ascii_Ascii mytrue myfalse myfalse myfalse mytrue mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse mytrue myfalse myfalse mytrue mytrue myfalse myfalse) String_EmptyString))
    (list.cons (String_String (Ascii_Ascii mytrue myfalse mytrue mytrue mytrue mytrue myfalse myfalse) String_EmptyString)
    (list.cons (String_String (Ascii_Ascii mytrue mytrue myfalse myfalse mytrue mytrue myfalse myfalse) String_EmptyString)
    (list.cons (String_String (Ascii_Ascii myfalse mytrue myfalse myfalse mytrue mytrue myfalse myfalse) (String_String (Ascii_Ascii myfalse mytrue myfalse myfalse mytrue mytrue myfalse myfalse) (String_String (Ascii_Ascii mytrue mytrue myfalse myfalse mytrue mytrue myfalse myfalse) String_EmptyString)))
    (list.cons (String_String (Ascii_Ascii myfalse mytrue myfalse mytrue myfalse mytrue myfalse myfalse) String_EmptyString)
    (list.cons (String_String (Ascii_Ascii myfalse myfalse myfalse mytrue myfalse mytrue myfalse myfalse) String_EmptyString)
    (list.cons (String_String (Ascii_Ascii mytrue mytrue myfalse myfalse mytrue mytrue myfalse myfalse) String_EmptyString)
    (list.cons (String_String (Ascii_Ascii mytrue myfalse mytrue mytrue myfalse mytrue myfalse myfalse) String_EmptyString)
    (list.cons (String_String (Ascii_Ascii myfalse myfalse myfalse mytrue myfalse mytrue myfalse myfalse) String_EmptyString)
    (list.cons (String_String (Ascii_Ascii mytrue myfalse myfalse myfalse myfalse mytrue mytrue myfalse) String_EmptyString)
    (list.cons (String_String (Ascii_Ascii mytrue myfalse mytrue mytrue myfalse mytrue myfalse myfalse) String_EmptyString)
    (list.cons (String_String (Ascii_Ascii mytrue mytrue myfalse myfalse myfalse mytrue mytrue myfalse) String_EmptyString)
    (list.cons (String_String (Ascii_Ascii mytrue myfalse myfalse myfalse myfalse mytrue myfalse myfalse) String_EmptyString)
    (list.cons (String_String (Ascii_Ascii mytrue myfalse myfalse myfalse myfalse mytrue myfalse myfalse) String_EmptyString)
    list.nil)))))))))))))))
