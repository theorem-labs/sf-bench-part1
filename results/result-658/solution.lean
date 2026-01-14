-- Lean translation of Rocq definitions for test_der0

set_option autoImplicit false

-- True type (for Prop True)
inductive True_ : Prop where
  | intro : True_

-- Boolean type (matching LF.Basics.bool)
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- Ascii type (8 bits) using Lean's built-in Bool
inductive Ascii_ascii : Type where
  | Ascii : Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool → Ascii_ascii

-- Helper to convert Nat bit to Bool
def nat_bit (n : Nat) : Bool :=
  n % 2 == 1

-- ascii_of_nat: convert a natural number to an ASCII character (8 bits)
def ascii_of_nat (n : Nat) : Ascii_ascii :=
  Ascii_ascii.Ascii
    (nat_bit n)
    (nat_bit (n / 2))
    (nat_bit (n / 4))
    (nat_bit (n / 8))
    (nat_bit (n / 16))
    (nat_bit (n / 32))
    (nat_bit (n / 64))
    (nat_bit (n / 128))

-- c = ascii_of_nat 99 = 'c'
-- 99 = 64 + 32 + 2 + 1 = 0b01100011
-- bits (LSB first): 1, 1, 0, 0, 0, 1, 1, 0
def Original_LF__DOT__IndProp_LF_IndProp_c : Ascii_ascii :=
  ascii_of_nat 99

-- Regular expression type
inductive Original_LF__DOT__IndProp_LF_IndProp_reg__exp (T : Type) : Type where
  | EmptySet : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | EmptyStr : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Char : T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | App : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Union : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Star : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T

-- EmptySet constructor as a function
def Original_LF__DOT__IndProp_LF_IndProp_EmptySet (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptySet

-- Equality in Prop (for Type)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality in Prop (for Prop)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- match_eps is Admitted in Original.v, so it's an axiom
axiom Original_LF__DOT__IndProp_LF_IndProp_match__eps :
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp Ascii_ascii → Original_LF__DOT__Basics_LF_Basics_bool

-- derive is Admitted in Original.v, so it's an axiom
axiom Original_LF__DOT__IndProp_LF_IndProp_derive :
  Ascii_ascii → Original_LF__DOT__IndProp_LF_IndProp_reg__exp Ascii_ascii → Original_LF__DOT__IndProp_LF_IndProp_reg__exp Ascii_ascii

-- test_der0 is Admitted in Original.v, so it's an axiom
axiom Original_LF__DOT__IndProp_LF_IndProp_test__der0 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__IndProp_LF_IndProp_match__eps
       (Original_LF__DOT__IndProp_LF_IndProp_derive
          Original_LF__DOT__IndProp_LF_IndProp_c
          (Original_LF__DOT__IndProp_LF_IndProp_EmptySet Ascii_ascii)))
    Original_LF__DOT__Basics_LF_Basics_false
