-- Lean translation of test_der7 and dependencies

set_option autoImplicit false

-- Define our own mybool to avoid stdlib issues
inductive mybool : Type where
  | mytrue : mybool
  | myfalse : mybool

-- Define ascii as 8 booleans
inductive Ascii_ascii : Type where
  | Ascii : mybool → mybool → mybool → mybool → mybool → mybool → mybool → mybool → Ascii_ascii

-- Boolean type (matching LF.Basics.bool)
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

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

-- App constructor as a function
def Original_LF__DOT__IndProp_LF_IndProp_App {T : Type} (r1 r2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.App r1 r2

-- The constant c = ascii_of_nat 99 = Ascii true true false false false true true false
-- 99 in binary is 01100011
-- b0 = 1, b1 = 1, b2 = 0, b3 = 0, b4 = 0, b5 = 1, b6 = 1, b7 = 0
def Original_LF__DOT__IndProp_LF_IndProp_c : Ascii_ascii :=
  Ascii_ascii.Ascii mybool.mytrue mybool.mytrue mybool.myfalse mybool.myfalse 
                    mybool.myfalse mybool.mytrue mybool.mytrue mybool.myfalse

-- The constant d = ascii_of_nat 100 = Ascii false false true false false true true false
-- 100 in binary is 01100100
-- b0 = 0, b1 = 0, b2 = 1, b3 = 0, b4 = 0, b5 = 1, b6 = 1, b7 = 0
def Original_LF__DOT__IndProp_LF_IndProp_d : Ascii_ascii :=
  Ascii_ascii.Ascii mybool.myfalse mybool.myfalse mybool.mytrue mybool.myfalse 
                    mybool.myfalse mybool.mytrue mybool.mytrue mybool.myfalse

-- The match_eps function (admitted in Rocq, so axiom in Lean)
axiom Original_LF__DOT__IndProp_LF_IndProp_match__eps : 
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp Ascii_ascii → Original_LF__DOT__Basics_LF_Basics_bool

-- The derive function (admitted in Rocq, so axiom in Lean)
axiom Original_LF__DOT__IndProp_LF_IndProp_derive : 
  Ascii_ascii → Original_LF__DOT__IndProp_LF_IndProp_reg__exp Ascii_ascii → Original_LF__DOT__IndProp_LF_IndProp_reg__exp Ascii_ascii

-- Equality in Prop (will become SProp in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl a

-- True in Prop (will become SProp in Rocq)
-- We use a different name to avoid clashing with Lean's True
inductive True_ : Prop where
  | intro : True_

-- test_der7: match_eps (derive d (derive c (App (Char d) (Char c)))) = false
-- This is Admitted in Original.v, so we declare it as an axiom
axiom Original_LF__DOT__IndProp_LF_IndProp_test__der7 : 
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__IndProp_LF_IndProp_match__eps 
      (Original_LF__DOT__IndProp_LF_IndProp_derive Original_LF__DOT__IndProp_LF_IndProp_d 
        (Original_LF__DOT__IndProp_LF_IndProp_derive Original_LF__DOT__IndProp_LF_IndProp_c 
          (Original_LF__DOT__IndProp_LF_IndProp_App 
            (Original_LF__DOT__IndProp_LF_IndProp_Char Original_LF__DOT__IndProp_LF_IndProp_d) 
            (Original_LF__DOT__IndProp_LF_IndProp_Char Original_LF__DOT__IndProp_LF_IndProp_c)))))
    Original_LF__DOT__Basics_LF_Basics_false
