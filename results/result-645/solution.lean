-- Lean translation for test_der1 and all dependencies

set_option autoImplicit false

-- Alias for True to avoid shadowing builtin
def MyTrue : Prop := _root_.True

def MyTrue_I : MyTrue := _root_.True.intro

-- Equality in Prop for Type arguments
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl a

-- recl for Corelib_Init_Logic_eq (needed for Rocq elimination)
def Corelib_Init_Logic_eq_recl {A : Type} (x : A) (motive : A → Corelib_Init_Logic_eq x x → Prop)
    (case_refl : motive x (Corelib_Init_Logic_eq.refl x)) (y : A) (h : Corelib_Init_Logic_eq x y) : motive x (Corelib_Init_Logic_eq.refl x) :=
  case_refl

-- Equality in Prop for Prop arguments (will be SProp in Rocq)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

def Corelib_Init_Logic_eq_Prop_refl {A : Prop} (a : A) : Corelib_Init_Logic_eq_Prop a a :=
  Corelib_Init_Logic_eq_Prop.refl a

-- Boolean type (matching LF.Basics.bool)
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_bool_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_bool_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

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

def Ascii_ascii_Ascii := @Ascii_ascii.Ascii

-- Projections for Ascii - needed for isomorphism proofs
-- Using a naming convention that matches the module/hyg pattern
def a____at___U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__test____der1__iso__hyg59 (a : Ascii_ascii) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match a with | Ascii_ascii.Ascii b0 _ _ _ _ _ _ _ => b0

def a____at___U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__test____der1__iso__hyg61 (a : Ascii_ascii) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match a with | Ascii_ascii.Ascii _ b1 _ _ _ _ _ _ => b1

def a____at___U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__test____der1__iso__hyg63 (a : Ascii_ascii) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match a with | Ascii_ascii.Ascii _ _ b2 _ _ _ _ _ => b2

def a____at___U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__test____der1__iso__hyg65 (a : Ascii_ascii) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match a with | Ascii_ascii.Ascii _ _ _ b3 _ _ _ _ => b3

def a____at___U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__test____der1__iso__hyg67 (a : Ascii_ascii) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match a with | Ascii_ascii.Ascii _ _ _ _ b4 _ _ _ => b4

def a____at___U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__test____der1__iso__hyg69 (a : Ascii_ascii) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match a with | Ascii_ascii.Ascii _ _ _ _ _ b5 _ _ => b5

def a____at___U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__test____der1__iso__hyg71 (a : Ascii_ascii) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match a with | Ascii_ascii.Ascii _ _ _ _ _ _ b6 _ => b6

def a____at___U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__test____der1__iso__hyg73 (a : Ascii_ascii) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match a with | Ascii_ascii.Ascii _ _ _ _ _ _ _ b7 => b7

-- indl for Ascii_ascii (for SProp elimination)
def Ascii_ascii_indl (motive : Ascii_ascii → Prop)
    (case_Ascii : ∀ b0 b1 b2 b3 b4 b5 b6 b7, motive (Ascii_ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7))
    (a : Ascii_ascii) : motive a :=
  match a with | Ascii_ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7 => case_Ascii b0 b1 b2 b3 b4 b5 b6 b7

-- Regular expression type
inductive Original_LF__DOT__IndProp_LF_IndProp_reg__exp (T : Type) : Type where
  | EmptySet : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | EmptyStr : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Char : T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | App : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Union : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Star : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T

-- Constructors as functions
def Original_LF__DOT__IndProp_LF_IndProp_reg__exp_EmptySet (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptySet

def Original_LF__DOT__IndProp_LF_IndProp_reg__exp_EmptyStr (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptyStr

def Original_LF__DOT__IndProp_LF_IndProp_reg__exp_Char {T : Type} (t : T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Char t

def Original_LF__DOT__IndProp_LF_IndProp_reg__exp_App {T : Type} (r1 r2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.App r1 r2

def Original_LF__DOT__IndProp_LF_IndProp_reg__exp_Union {T : Type} (r1 r2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Union r1 r2

def Original_LF__DOT__IndProp_LF_IndProp_reg__exp_Star {T : Type} (r : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star r

-- Char constructor as a function
def Original_LF__DOT__IndProp_LF_IndProp_Char {T : Type} (t : T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Char t

-- The character 'c' = ASCII 99 = binary 01100011
-- In Coq: Ascii true true false false false true true false
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

-- The test_der1 theorem (axiom since Admitted in Original.v)
-- test_der1 : match_eps (derive c (Char c)) = true
axiom Original_LF__DOT__IndProp_LF_IndProp_test__der1 : 
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__IndProp_LF_IndProp_match__eps 
      (Original_LF__DOT__IndProp_LF_IndProp_derive Original_LF__DOT__IndProp_LF_IndProp_c 
        (Original_LF__DOT__IndProp_LF_IndProp_Char Original_LF__DOT__IndProp_LF_IndProp_c))) 
    Original_LF__DOT__Basics_LF_Basics_true
