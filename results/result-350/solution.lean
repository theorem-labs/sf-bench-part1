-- Definitions for the translation

-- nat type (define our own to avoid stdlib issues)
inductive nat : Type where
  | O : nat
  | S : nat → nat

-- String type (define our own simple version)
inductive ascii : Type where
  | Ascii : Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool → ascii

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

-- Alias for None to match expected name
def Original_LF__DOT__Poly_LF_Poly_None {X : Type} : Original_LF__DOT__Poly_LF_Poly_option X :=
  Original_LF__DOT__Poly_LF_Poly_option.None

-- The main definition: manual_grade_for_not_PNP_informal is None of option (nat * string)
def Original_LF__DOT__Logic_LF_Logic_manual__grade__for__not__PNP__informal : 
    Original_LF__DOT__Poly_LF_Poly_option (Original_LF__DOT__Poly_LF_Poly_prod nat String_string) :=
  Original_LF__DOT__Poly_LF_Poly_option.None
