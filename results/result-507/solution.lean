-- Lean 4 translation for manual_grade_for_re_opt_match'' and all dependencies

-- nat type (matching Rocq nat)
inductive nat : Type where
  | O : nat
  | S : nat → nat

-- Standard bool for ascii (matches Stdlib.Init.Datatypes.bool)
inductive Stdlib_bool : Type where
  | true : Stdlib_bool
  | false : Stdlib_bool

-- Ascii type (8 booleans)
inductive Ascii_ascii : Type where
  | Ascii : Stdlib_bool → Stdlib_bool → Stdlib_bool → Stdlib_bool → 
            Stdlib_bool → Stdlib_bool → Stdlib_bool → Stdlib_bool → Ascii_ascii

-- List type (matching Original.LF_DOT_Poly.LF.Poly.list)
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

-- String is a type alias for list of ascii
def Original_LF__DOT__IndProp_LF_IndProp_string : Type := 
  Original_LF__DOT__Poly_LF_Poly_list Ascii_ascii

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

-- manual_grade_for_re_opt_match'' is None of type option (nat*string)
-- where string = list ascii
def Original_LF__DOT__AltAuto_LF_AltAuto_manual__grade__for__re__opt__match'' :
    Original_LF__DOT__Poly_LF_Poly_option (Original_LF__DOT__Poly_LF_Poly_prod nat Original_LF__DOT__IndProp_LF_IndProp_string) :=
  Original_LF__DOT__Poly_LF_Poly_option.None
