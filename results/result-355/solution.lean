-- Definitions for nat, String, option, prod, and the main value
-- Using custom types to avoid Lean stdlib pollution

-- Bool type (renamed to avoid conflict with Lean's Bool)
inductive mybool : Type where
  | true : mybool
  | false : mybool

-- nat type (custom definition to avoid importing Lean's Nat)
inductive nat : Type where
  | O : nat
  | S : nat → nat

-- ascii type (8 bools)
inductive ascii : Type where
  | Ascii : mybool → mybool → mybool → mybool → mybool → mybool → mybool → mybool → ascii

-- string type (list of ascii)
inductive String_string : Type where
  | EmptyString : String_string
  | String : ascii → String_string → String_string

-- prod type (matching Original.LF_DOT_Poly.LF.Poly.prod)
inductive Original_LF__DOT__Poly_LF_Poly_prod (X Y : Type) : Type where
  | pair : X → Y → Original_LF__DOT__Poly_LF_Poly_prod X Y

-- option type (matching Original.LF_DOT_Poly.LF.Poly.option)
inductive Original_LF__DOT__Poly_LF_Poly_option (X : Type) : Type where
  | Some : X → Original_LF__DOT__Poly_LF_Poly_option X
  | None : Original_LF__DOT__Poly_LF_Poly_option X

-- Alias for None constructor
def Original_LF__DOT__Poly_LF_Poly_None (X : Type) : Original_LF__DOT__Poly_LF_Poly_option X :=
  Original_LF__DOT__Poly_LF_Poly_option.None

-- The main definition
def Original_LF__DOT__Logic_LF_Logic_manual__grade__for__double__neg__informal : 
  Original_LF__DOT__Poly_LF_Poly_option (Original_LF__DOT__Poly_LF_Poly_prod nat String_string) := 
  Original_LF__DOT__Poly_LF_Poly_option.None
