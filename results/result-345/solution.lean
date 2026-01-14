-- Definitions for nat, String.string, prod, option, and manual_grade_for_informal_proof

set_option autoImplicit false

-- nat type
inductive nat : Type where
  | O : nat
  | S : nat → nat

namespace Datatypes

-- bool type
inductive bool : Type where
  | true : bool
  | false : bool

end Datatypes

-- Ascii.ascii type (8 bools)
inductive Ascii_ascii : Type where
  | Ascii : Datatypes.bool → Datatypes.bool → Datatypes.bool → Datatypes.bool → Datatypes.bool → Datatypes.bool → Datatypes.bool → Datatypes.bool → Ascii_ascii

-- String.string type
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

-- manual_grade_for_informal_proof = None : option (nat * string)
def Original_LF__DOT__Tactics_LF_Tactics_manual__grade__for__informal__proof : 
    Original_LF__DOT__Poly_LF_Poly_option (Original_LF__DOT__Poly_LF_Poly_prod nat String_string) :=
  Original_LF__DOT__Poly_LF_Poly_option.None
