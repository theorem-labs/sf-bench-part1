-- Lean translation for String.string and the value W

-- Boolean type (matching Rocq's bool)
inductive Mybool : Type where
  | true : Mybool
  | false : Mybool

-- ASCII character (8 bools, matching Rocq's Ascii.ascii)
inductive Ascii_ascii : Type where
  | Ascii : Mybool → Mybool → Mybool → Mybool → Mybool → Mybool → Mybool → Mybool → Ascii_ascii

-- String type (matching Rocq's String.string)
inductive String_string : Type where
  | EmptyString : String_string
  | String : Ascii_ascii → String_string → String_string

-- The value W = "w" (lowercase w, ASCII 119 = 01110111 in binary)
-- Rocq: Ascii.Ascii true true true false true false true false
def Original_LF__DOT__Imp_LF_Imp_W : String_string :=
  String_string.String
    (Ascii_ascii.Ascii Mybool.true Mybool.true Mybool.true Mybool.false Mybool.true Mybool.false Mybool.true Mybool.false)
    String_string.EmptyString
