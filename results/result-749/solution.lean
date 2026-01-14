-- Complete Lean translation for test_der6 and all dependencies

set_option autoImplicit false

-- Boolean type (matching Rocq bool with true first)
inductive mybool : Type where
  | mytrue : mybool
  | myfalse : mybool

-- Aliases for export
def mybool_true := mybool.mytrue
def mybool_false := mybool.myfalse

-- True in SProp
inductive MyTrue : Prop where
  | intro : MyTrue

-- Equality in Prop (will become SProp in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl a

-- Boolean type (matching LF.Basics.bool)
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- ASCII character type (8 bits)
inductive Ascii_ascii : Type where
  | Ascii : mybool → mybool → mybool → mybool → mybool → mybool → mybool → mybool → Ascii_ascii

def Ascii_Ascii : mybool → mybool → mybool → mybool → mybool → mybool → mybool → mybool → Ascii_ascii :=
  Ascii_ascii.Ascii

-- Regular expression type
inductive Original_LF__DOT__IndProp_LF_IndProp_reg__exp (T : Type) : Type where
  | EmptySet : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | EmptyStr : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Char : T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | App : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Union : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Star : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T

-- Constructors as functions
def Original_LF__DOT__IndProp_LF_IndProp_EmptySet (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptySet

def Original_LF__DOT__IndProp_LF_IndProp_EmptyStr (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptyStr

def Original_LF__DOT__IndProp_LF_IndProp_Char {T : Type} (t : T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Char t

def Original_LF__DOT__IndProp_LF_IndProp_App {T : Type} (r1 r2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.App r1 r2

def Original_LF__DOT__IndProp_LF_IndProp_Union {T : Type} (r1 r2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Union r1 r2

def Original_LF__DOT__IndProp_LF_IndProp_Star {T : Type} (r : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star r

-- Character 'c' = ASCII 99 = binary 01100011
-- Reading from bit 0 to bit 7: true true false false false true true false
def Original_LF__DOT__IndProp_LF_IndProp_c : Ascii_ascii :=
  Ascii_ascii.Ascii mybool.mytrue mybool.mytrue mybool.myfalse mybool.myfalse mybool.myfalse mybool.mytrue mybool.mytrue mybool.myfalse

-- Character 'd' = ASCII 100 = binary 01100100
-- Reading from bit 0 to bit 7: false false true false false true true false
def Original_LF__DOT__IndProp_LF_IndProp_d : Ascii_ascii :=
  Ascii_ascii.Ascii mybool.myfalse mybool.myfalse mybool.mytrue mybool.myfalse mybool.myfalse mybool.mytrue mybool.mytrue mybool.myfalse

-- match_eps function (admitted in Original.v, so axiom here)
axiom Original_LF__DOT__IndProp_LF_IndProp_match__eps :
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp Ascii_ascii → Original_LF__DOT__Basics_LF_Basics_bool

-- derive function (admitted in Original.v, so axiom here)
axiom Original_LF__DOT__IndProp_LF_IndProp_derive :
  Ascii_ascii → Original_LF__DOT__IndProp_LF_IndProp_reg__exp Ascii_ascii → Original_LF__DOT__IndProp_LF_IndProp_reg__exp Ascii_ascii

-- test_der6 theorem (admitted in Original.v, so axiom here)
-- match_eps (derive d (derive c (App (Char c) (Char d)))) = true
axiom Original_LF__DOT__IndProp_LF_IndProp_test__der6 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__IndProp_LF_IndProp_match__eps
       (Original_LF__DOT__IndProp_LF_IndProp_derive Original_LF__DOT__IndProp_LF_IndProp_d
          (Original_LF__DOT__IndProp_LF_IndProp_derive Original_LF__DOT__IndProp_LF_IndProp_c
             (Original_LF__DOT__IndProp_LF_IndProp_App
                (Original_LF__DOT__IndProp_LF_IndProp_Char Original_LF__DOT__IndProp_LF_IndProp_c)
                (Original_LF__DOT__IndProp_LF_IndProp_Char Original_LF__DOT__IndProp_LF_IndProp_d)))))
    Original_LF__DOT__Basics_LF_Basics_true
