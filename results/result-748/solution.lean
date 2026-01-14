-- Lean translation for test_der3 and all dependencies

set_option autoImplicit false

-- True type (will become SProp in Rocq)
inductive MyTrue : Prop where
  | intro : MyTrue

-- Equality in Prop
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl a

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

-- EmptyStr constructor as a function (polymorphic version)
def Original_LF__DOT__IndProp_LF_IndProp_EmptyStr (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptyStr

-- Char constructor as a function
def Original_LF__DOT__IndProp_LF_IndProp_Char {T : Type} (t : T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Char t

-- App constructor as a function
def Original_LF__DOT__IndProp_LF_IndProp_App {T : Type} (r1 r2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.App r1 r2

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

-- The test_der3 theorem (axiom since Admitted in Original.v)
-- test_der3 : match_eps (derive c (App (Char c) EmptyStr)) = true
axiom Original_LF__DOT__IndProp_LF_IndProp_test__der3 : 
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__IndProp_LF_IndProp_match__eps 
      (Original_LF__DOT__IndProp_LF_IndProp_derive Original_LF__DOT__IndProp_LF_IndProp_c 
        (Original_LF__DOT__IndProp_LF_IndProp_App 
          (Original_LF__DOT__IndProp_LF_IndProp_Char Original_LF__DOT__IndProp_LF_IndProp_c) 
          (Original_LF__DOT__IndProp_LF_IndProp_EmptyStr Ascii_ascii)))) 
    Original_LF__DOT__Basics_LF_Basics_true
