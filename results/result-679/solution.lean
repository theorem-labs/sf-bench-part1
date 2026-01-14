-- Lean translation of Rocq Imp language definitions
-- Matching the Rocq types exactly for isomorphism

-- Define mybool to match Coq's bool
inductive mybool : Type where
  | mytrue : mybool
  | myfalse : mybool

-- Natural numbers matching nat
inductive mynat : Type where
  | O : mynat
  | S : mynat → mynat

-- Define ascii to match Ascii.ascii (8 bools)
inductive Ascii_ascii : Type where
  | Ascii : mybool → mybool → mybool → mybool → mybool → mybool → mybool → mybool → Ascii_ascii

-- String as a list of Ascii, matching String.string
inductive String_string : Type where
  | EmptyString : String_string
  | String : Ascii_ascii → String_string → String_string

-- Arithmetic expressions matching Original.LF_DOT_Imp.LF.Imp.aexp
inductive Original_LF__DOT__Imp_LF_Imp_aexp : Type where
  | ANum : mynat → Original_LF__DOT__Imp_LF_Imp_aexp
  | AId : String_string → Original_LF__DOT__Imp_LF_Imp_aexp
  | APlus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp
  | AMinus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp
  | AMult : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp

-- Boolean expressions matching Original.LF_DOT_Imp.LF.Imp.bexp
inductive Original_LF__DOT__Imp_LF_Imp_bexp : Type where
  | BTrue : Original_LF__DOT__Imp_LF_Imp_bexp
  | BFalse : Original_LF__DOT__Imp_LF_Imp_bexp
  | BEq : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BNeq : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BLe : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BGt : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BNot : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BAnd : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp

-- Commands matching Original.LF_DOT_Imp.LF.Imp.com
inductive Original_LF__DOT__Imp_LF_Imp_com : Type where
  | CSkip : Original_LF__DOT__Imp_LF_Imp_com
  | CAsgn : String_string → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_com
  | CSeq : Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com
  | CIf : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com
  | CWhile : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com

-- Helper for building strings - "X" is the character 'X' = ASCII 88 = 01011000
-- Bit order in Ascii constructor: b0 b1 b2 b3 b4 b5 b6 b7 (LSB first)
-- 'X' = 88 = 0b01011000, LSB first: 0,0,0,1,1,0,1,0
def charX : Ascii_ascii := Ascii_ascii.Ascii mybool.myfalse mybool.myfalse mybool.myfalse mybool.mytrue mybool.mytrue mybool.myfalse mybool.mytrue mybool.myfalse
-- 'Y' = 89 = 0b01011001, LSB first: 1,0,0,1,1,0,1,0
def charY : Ascii_ascii := Ascii_ascii.Ascii mybool.mytrue mybool.myfalse mybool.myfalse mybool.mytrue mybool.mytrue mybool.myfalse mybool.mytrue mybool.myfalse
-- 'Z' = 90 = 0b01011010, LSB first: 0,1,0,1,1,0,1,0
def charZ : Ascii_ascii := Ascii_ascii.Ascii mybool.myfalse mybool.mytrue mybool.myfalse mybool.mytrue mybool.mytrue mybool.myfalse mybool.mytrue mybool.myfalse

-- Variables
def Original_LF__DOT__Imp_LF_Imp_X : String_string := String_string.String charX String_string.EmptyString
def Original_LF__DOT__Imp_LF_Imp_Y : String_string := String_string.String charY String_string.EmptyString
def Original_LF__DOT__Imp_LF_Imp_Z : String_string := String_string.String charZ String_string.EmptyString

-- XtimesYinZ = <{ Z := X * Y }> = CAsgn Z (AMult (AId X) (AId Y))
def Original_LF__DOT__Imp_LF_Imp_XtimesYinZ : Original_LF__DOT__Imp_LF_Imp_com :=
  Original_LF__DOT__Imp_LF_Imp_com.CAsgn
    Original_LF__DOT__Imp_LF_Imp_Z
    (Original_LF__DOT__Imp_LF_Imp_aexp.AMult
      (Original_LF__DOT__Imp_LF_Imp_aexp.AId Original_LF__DOT__Imp_LF_Imp_X)
      (Original_LF__DOT__Imp_LF_Imp_aexp.AId Original_LF__DOT__Imp_LF_Imp_Y))

-- Export constructor aliases for the isomorphism proofs
def Original_LF__DOT__Imp_LF_Imp_AId := Original_LF__DOT__Imp_LF_Imp_aexp.AId
def Original_LF__DOT__Imp_LF_Imp_AMult := Original_LF__DOT__Imp_LF_Imp_aexp.AMult
def Original_LF__DOT__Imp_LF_Imp_CAsgn := Original_LF__DOT__Imp_LF_Imp_com.CAsgn
