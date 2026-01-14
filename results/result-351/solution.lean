-- Definitions for nat, String.string, option, prod, and manual_grade_for_nostutter
-- Using custom types to avoid Lean stdlib issues

-- nat type
inductive nat : Type where
  | O : nat
  | S : nat → nat

-- Ascii character (8 bits)
inductive ascii : Type where
  | Ascii : Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool → ascii

-- String type (matching Rocq's String.string)
inductive String_string : Type where
  | EmptyString : String_string
  | String : ascii → String_string → String_string

-- Prod type (matching Original.LF_DOT_Poly.LF.Poly.prod)
inductive Original_LF__DOT__Poly_LF_Poly_prod (X Y : Type) : Type where
  | pair : X → Y → Original_LF__DOT__Poly_LF_Poly_prod X Y

-- Option type (matching Original.LF_DOT_Poly.LF.Poly.option)
inductive Original_LF__DOT__Poly_LF_Poly_option (X : Type) : Type where
  | Some : X → Original_LF__DOT__Poly_LF_Poly_option X
  | None : Original_LF__DOT__Poly_LF_Poly_option X

-- None constructor as a definition (for the checker)
def Original_LF__DOT__Poly_LF_Poly_None (X : Type) : Original_LF__DOT__Poly_LF_Poly_option X :=
  Original_LF__DOT__Poly_LF_Poly_option.None

-- manual_grade_for_nostutter = None : option (nat * string)
def Original_LF__DOT__IndProp_LF_IndProp_manual__grade__for__nostutter : 
  Original_LF__DOT__Poly_LF_Poly_option (Original_LF__DOT__Poly_LF_Poly_prod nat String_string) :=
  Original_LF__DOT__Poly_LF_Poly_option.None
