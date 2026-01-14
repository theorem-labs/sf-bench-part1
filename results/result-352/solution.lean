-- Definitions for nat, String.string, option, prod

-- nat type 
inductive nat : Type where
  | O : nat
  | S : nat → nat

-- ascii type (8 bits)
inductive ascii : Type where
  | Ascii : Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool → ascii

-- String type - matching Rocq's String.string (inductive with EmptyString and String)
inductive String_string : Type where
  | EmptyString : String_string
  | String : ascii → String_string → String_string

-- option type (matching Original.LF_DOT_Poly.LF.Poly.option)
inductive Original_LF__DOT__Poly_LF_Poly_option (X : Type) : Type where
  | Some : X → Original_LF__DOT__Poly_LF_Poly_option X
  | None : Original_LF__DOT__Poly_LF_Poly_option X

-- prod type (matching Original.LF_DOT_Poly.LF.Poly.prod)
inductive Original_LF__DOT__Poly_LF_Poly_prod (X Y : Type) : Type where
  | pair : X → Y → Original_LF__DOT__Poly_LF_Poly_prod X Y

-- None constructor 
def Original_LF__DOT__Poly_LF_Poly_None (X : Type) : Original_LF__DOT__Poly_LF_Poly_option X := 
  Original_LF__DOT__Poly_LF_Poly_option.None

-- The main value: manual_grade_for_NoDup_disjoint_etc : option (nat*string) := None
def Original_LF__DOT__IndProp_LF_IndProp_manual__grade__for__NoDup__disjoint__etc : 
  Original_LF__DOT__Poly_LF_Poly_option (Original_LF__DOT__Poly_LF_Poly_prod nat String_string) := 
  Original_LF__DOT__Poly_LF_Poly_option.None
