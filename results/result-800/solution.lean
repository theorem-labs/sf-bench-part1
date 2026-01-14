/-
  Lean translation of Imp definitions from LF.Imp
-/

set_option linter.unusedVariables false

-- Bool type with constructors
inductive Bool' where
  | true : Bool'
  | false : Bool'

def Bool'_true := Bool'.true
def Bool'_false := Bool'.false

-- Nat alias  
def nat := Nat

def nat_O : nat := Nat.zero
def nat_S (n : nat) : nat := Nat.succ n

-- Ascii type
structure Ascii_ascii where
  a0 : Bool'
  a1 : Bool'
  a2 : Bool'
  a3 : Bool'
  a4 : Bool'
  a5 : Bool'
  a6 : Bool'
  a7 : Bool'

def Ascii_ascii_Ascii := Ascii_ascii.mk

-- String type
inductive String_string where
  | EmptyString : String_string
  | String : Ascii_ascii → String_string → String_string

def String_string_EmptyString := String_string.EmptyString
def String_string_String := String_string.String

-- aexp type (arithmetic expressions)
inductive Original_LF__DOT__Imp_LF_Imp_aexp where
  | ANum : nat → Original_LF__DOT__Imp_LF_Imp_aexp
  | AId : String_string → Original_LF__DOT__Imp_LF_Imp_aexp
  | APlus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp
  | AMinus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp
  | AMult : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp

def Original_LF__DOT__Imp_LF_Imp_aexp_ANum := Original_LF__DOT__Imp_LF_Imp_aexp.ANum
def Original_LF__DOT__Imp_LF_Imp_aexp_AId := Original_LF__DOT__Imp_LF_Imp_aexp.AId
def Original_LF__DOT__Imp_LF_Imp_aexp_APlus := Original_LF__DOT__Imp_LF_Imp_aexp.APlus
def Original_LF__DOT__Imp_LF_Imp_aexp_AMinus := Original_LF__DOT__Imp_LF_Imp_aexp.AMinus
def Original_LF__DOT__Imp_LF_Imp_aexp_AMult := Original_LF__DOT__Imp_LF_Imp_aexp.AMult

-- bexp type (boolean expressions)
inductive Original_LF__DOT__Imp_LF_Imp_bexp where
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

-- com type (commands)
inductive Original_LF__DOT__Imp_LF_Imp_com where
  | CSkip : Original_LF__DOT__Imp_LF_Imp_com
  | CAsgn : String_string → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_com
  | CSeq : Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com
  | CIf : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com
  | CWhile : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com

def Original_LF__DOT__Imp_LF_Imp_com_CSkip := Original_LF__DOT__Imp_LF_Imp_com.CSkip
def Original_LF__DOT__Imp_LF_Imp_com_CAsgn := Original_LF__DOT__Imp_LF_Imp_com.CAsgn
def Original_LF__DOT__Imp_LF_Imp_com_CSeq := Original_LF__DOT__Imp_LF_Imp_com.CSeq
def Original_LF__DOT__Imp_LF_Imp_com_CIf := Original_LF__DOT__Imp_LF_Imp_com.CIf
def Original_LF__DOT__Imp_LF_Imp_com_CWhile := Original_LF__DOT__Imp_LF_Imp_com.CWhile

-- X : string = "X"
-- 'X' = 88 = 0b01011000, bits are b0..b7 (LSB to MSB)
def Original_LF__DOT__Imp_LF_Imp_X : String_string :=
  String_string.String 
    (Ascii_ascii.mk Bool'.false Bool'.false Bool'.false Bool'.true Bool'.true Bool'.false Bool'.true Bool'.false)
    String_string.EmptyString

-- Z : string = "Z"
-- 'Z' = 90 = 0b01011010, bits are b0..b7 (LSB to MSB)
def Original_LF__DOT__Imp_LF_Imp_Z : String_string :=
  String_string.String
    (Ascii_ascii.mk Bool'.false Bool'.true Bool'.false Bool'.true Bool'.true Bool'.false Bool'.true Bool'.false)
    String_string.EmptyString

-- ANum constructor 
def Original_LF__DOT__Imp_LF_Imp_ANum := Original_LF__DOT__Imp_LF_Imp_aexp.ANum

-- AId constructor
def Original_LF__DOT__Imp_LF_Imp_AId := Original_LF__DOT__Imp_LF_Imp_aexp.AId

-- AMinus constructor
def Original_LF__DOT__Imp_LF_Imp_AMinus := Original_LF__DOT__Imp_LF_Imp_aexp.AMinus

-- CAsgn constructor
def Original_LF__DOT__Imp_LF_Imp_CAsgn := Original_LF__DOT__Imp_LF_Imp_com.CAsgn

-- CSeq constructor
def Original_LF__DOT__Imp_LF_Imp_CSeq := Original_LF__DOT__Imp_LF_Imp_com.CSeq

-- CWhile constructor
def Original_LF__DOT__Imp_LF_Imp_CWhile := Original_LF__DOT__Imp_LF_Imp_com.CWhile

-- subtract_slowly_body: Z := Z - 1; X := X - 1
def Original_LF__DOT__Imp_LF_Imp_subtract__slowly__body : Original_LF__DOT__Imp_LF_Imp_com :=
  Original_LF__DOT__Imp_LF_Imp_com.CSeq
    (Original_LF__DOT__Imp_LF_Imp_com.CAsgn 
      Original_LF__DOT__Imp_LF_Imp_Z
      (Original_LF__DOT__Imp_LF_Imp_aexp.AMinus 
        (Original_LF__DOT__Imp_LF_Imp_aexp.AId Original_LF__DOT__Imp_LF_Imp_Z)
        (Original_LF__DOT__Imp_LF_Imp_aexp.ANum (nat_S nat_O))))
    (Original_LF__DOT__Imp_LF_Imp_com.CAsgn
      Original_LF__DOT__Imp_LF_Imp_X
      (Original_LF__DOT__Imp_LF_Imp_aexp.AMinus
        (Original_LF__DOT__Imp_LF_Imp_aexp.AId Original_LF__DOT__Imp_LF_Imp_X)
        (Original_LF__DOT__Imp_LF_Imp_aexp.ANum (nat_S nat_O))))

-- subtract_slowly: while X <> 0 do subtract_slowly_body end
def Original_LF__DOT__Imp_LF_Imp_subtract__slowly : Original_LF__DOT__Imp_LF_Imp_com :=
  Original_LF__DOT__Imp_LF_Imp_com.CWhile
    (Original_LF__DOT__Imp_LF_Imp_bexp.BNeq
      (Original_LF__DOT__Imp_LF_Imp_aexp.AId Original_LF__DOT__Imp_LF_Imp_X)
      (Original_LF__DOT__Imp_LF_Imp_aexp.ANum nat_O))
    Original_LF__DOT__Imp_LF_Imp_subtract__slowly__body

-- Helper to build nat from number
def mkNat : Nat → nat := id

-- subtract_3_from_5_slowly: X := 3; Z := 5; subtract_slowly
def Original_LF__DOT__Imp_LF_Imp_subtract__3__from__5__slowly : Original_LF__DOT__Imp_LF_Imp_com :=
  Original_LF__DOT__Imp_LF_Imp_com.CSeq
    (Original_LF__DOT__Imp_LF_Imp_com.CAsgn
      Original_LF__DOT__Imp_LF_Imp_X
      (Original_LF__DOT__Imp_LF_Imp_aexp.ANum (nat_S (nat_S (nat_S nat_O))))) -- 3
    (Original_LF__DOT__Imp_LF_Imp_com.CSeq
      (Original_LF__DOT__Imp_LF_Imp_com.CAsgn
        Original_LF__DOT__Imp_LF_Imp_Z
        (Original_LF__DOT__Imp_LF_Imp_aexp.ANum (nat_S (nat_S (nat_S (nat_S (nat_S nat_O))))))) -- 5
      Original_LF__DOT__Imp_LF_Imp_subtract__slowly)
