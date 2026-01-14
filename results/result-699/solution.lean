-- Lean translation for test_der5 and all dependencies

set_option autoImplicit false

-- True type (will become SProp in Rocq)
-- We use a custom name to avoid conflict with Lean's True
inductive MyTrue : Prop where
  | intro : MyTrue

-- Equality in Prop (for Type arguments)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl a

-- Equality in Prop (for Prop arguments)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

def Corelib_Init_Logic_eq_Prop_refl {A : Prop} (a : A) : Corelib_Init_Logic_eq_Prop a a :=
  Corelib_Init_Logic_eq_Prop.refl a

-- Boolean type (matching LF.Basics.bool) - using custom bool to avoid Lean's Bool
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- Ascii type (8 booleans) - using our custom bool
inductive Ascii_ascii : Type where
  | Ascii : Original_LF__DOT__Basics_LF_Basics_bool → Original_LF__DOT__Basics_LF_Basics_bool → 
            Original_LF__DOT__Basics_LF_Basics_bool → Original_LF__DOT__Basics_LF_Basics_bool → 
            Original_LF__DOT__Basics_LF_Basics_bool → Original_LF__DOT__Basics_LF_Basics_bool → 
            Original_LF__DOT__Basics_LF_Basics_bool → Original_LF__DOT__Basics_LF_Basics_bool → Ascii_ascii

-- Regular expression type
inductive Original_LF__DOT__IndProp_LF_IndProp_reg__exp (T : Type) : Type where
  | EmptySet : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | EmptyStr : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Char : T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | App : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Union : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Star : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T

-- Char constructor as a function
def Original_LF__DOT__IndProp_LF_IndProp_Char {T : Type} (t : T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Char t

-- Star constructor as a function
def Original_LF__DOT__IndProp_LF_IndProp_Star {T : Type} (r : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star r

-- The character 'c' = ASCII 99 = binary 01100011
-- In Coq: Ascii true true false false false true true false
-- Reading from bit 0 to bit 7: 1,1,0,0,0,1,1,0
def Original_LF__DOT__IndProp_LF_IndProp_c : Ascii_ascii :=
  Ascii_ascii.Ascii Original_LF__DOT__Basics_LF_Basics_bool.true 
                    Original_LF__DOT__Basics_LF_Basics_bool.true 
                    Original_LF__DOT__Basics_LF_Basics_bool.false 
                    Original_LF__DOT__Basics_LF_Basics_bool.false 
                    Original_LF__DOT__Basics_LF_Basics_bool.false 
                    Original_LF__DOT__Basics_LF_Basics_bool.true 
                    Original_LF__DOT__Basics_LF_Basics_bool.true 
                    Original_LF__DOT__Basics_LF_Basics_bool.false

-- The derive function (axiom since Admitted in Original.v)
axiom Original_LF__DOT__IndProp_LF_IndProp_derive : 
  Ascii_ascii → Original_LF__DOT__IndProp_LF_IndProp_reg__exp Ascii_ascii → Original_LF__DOT__IndProp_LF_IndProp_reg__exp Ascii_ascii

-- The match_eps function (axiom since Admitted in Original.v)
axiom Original_LF__DOT__IndProp_LF_IndProp_match__eps : 
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp Ascii_ascii → Original_LF__DOT__Basics_LF_Basics_bool

-- The test_der5 theorem (axiom since Admitted in Original.v)
-- test_der5 : match_eps (derive c (Star (Char c))) = true
axiom Original_LF__DOT__IndProp_LF_IndProp_test__der5 : 
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__IndProp_LF_IndProp_match__eps 
      (Original_LF__DOT__IndProp_LF_IndProp_derive Original_LF__DOT__IndProp_LF_IndProp_c 
        (Original_LF__DOT__IndProp_LF_IndProp_Star 
          (Original_LF__DOT__IndProp_LF_IndProp_Char Original_LF__DOT__IndProp_LF_IndProp_c)))) 
    Original_LF__DOT__Basics_LF_Basics_true
