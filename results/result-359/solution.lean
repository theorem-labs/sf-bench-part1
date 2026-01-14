-- Lean 4 translation for the Rocq definitions

-- nat type (matching Rocq nat)
inductive nat : Type where
  | O : nat
  | S : nat → nat

-- String.string (matching Rocq String.string)
-- First, define Ascii.ascii (8 bits)
inductive mybool : Type where
  | true : mybool
  | false : mybool

inductive Ascii_ascii : Type where
  | Ascii : mybool → mybool → mybool → mybool → mybool → mybool → mybool → mybool → Ascii_ascii

inductive String_string : Type where
  | EmptyString : String_string
  | String : Ascii_ascii → String_string → String_string

-- Prod type (matching Original.LF_DOT_Poly.LF.Poly.prod)
inductive Original_LF__DOT__Poly_LF_Poly_prod (X Y : Type) : Type where
  | pair : X → Y → Original_LF__DOT__Poly_LF_Poly_prod X Y

-- Option type (matching Original.LF_DOT_Poly.LF.Poly.option)
inductive Original_LF__DOT__Poly_LF_Poly_option (X : Type) : Type where
  | Some : X → Original_LF__DOT__Poly_LF_Poly_option X
  | None : Original_LF__DOT__Poly_LF_Poly_option X

-- None constructor
def Original_LF__DOT__Poly_LF_Poly_None (X : Type) : Original_LF__DOT__Poly_LF_Poly_option X :=
  Original_LF__DOT__Poly_LF_Poly_option.None

-- manual_grade_for_R_provability is None of type option (nat*string)
def Original_LF__DOT__IndProp_LF_IndProp_manual__grade__for__R__provability :
    Original_LF__DOT__Poly_LF_Poly_option (Original_LF__DOT__Poly_LF_Poly_prod nat String_string) :=
  Original_LF__DOT__Poly_LF_Poly_option.None
