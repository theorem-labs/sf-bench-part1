/-
  Lean translation of derives and all dependencies from LF.IndProp
-/

set_option autoImplicit false

-- Standard bool for ascii (matches Stdlib.Init.Datatypes.bool)
inductive Stdlib_bool : Type where
  | true : Stdlib_bool
  | false : Stdlib_bool

-- Alias for bool
def Datatypes_bool := Stdlib_bool
def Datatypes_true := Stdlib_bool.true
def Datatypes_false := Stdlib_bool.false

-- Ascii type (8 booleans)
inductive Ascii_ascii : Type where
  | Ascii : Stdlib_bool → Stdlib_bool → Stdlib_bool → Stdlib_bool → 
            Stdlib_bool → Stdlib_bool → Stdlib_bool → Stdlib_bool → Ascii_ascii

-- List type (matching Original.LF_DOT_Poly.LF.Poly.list)
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

-- Alias for cons
def Original_LF__DOT__Poly_LF_Poly_cons (X : Type) : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons

-- Alias for nil 
def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

-- app function for lists
def Original_LF__DOT__Poly_LF_Poly_app {X : Type} : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X
  | Original_LF__DOT__Poly_LF_Poly_list.nil, l2 => l2
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t, l2 => Original_LF__DOT__Poly_LF_Poly_list.cons h (Original_LF__DOT__Poly_LF_Poly_app t l2)

-- Regular expression type (matching Original.LF_DOT_IndProp.LF.IndProp.reg_exp)
inductive Original_LF__DOT__IndProp_LF_IndProp_reg__exp (T : Type) : Type where
  | EmptySet : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | EmptyStr : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Char : T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | App : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Union : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Star : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T

-- Aliases for reg_exp constructors
def Original_LF__DOT__IndProp_LF_IndProp_EmptySet (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T := Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptySet
def Original_LF__DOT__IndProp_LF_IndProp_EmptyStr (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T := Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptyStr
def Original_LF__DOT__IndProp_LF_IndProp_Char (T : Type) : T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T := Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Char
def Original_LF__DOT__IndProp_LF_IndProp_App (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T := Original_LF__DOT__IndProp_LF_IndProp_reg__exp.App
def Original_LF__DOT__IndProp_LF_IndProp_Union (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T := Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Union
def Original_LF__DOT__IndProp_LF_IndProp_Star (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T := Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star

-- exp_match inductive (matching Original.LF_DOT_IndProp.LF.IndProp.exp_match)
inductive Original_LF__DOT__IndProp_LF_IndProp_exp__match {T : Type} : Original_LF__DOT__Poly_LF_Poly_list T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Prop where
  | MEmpty : Original_LF__DOT__IndProp_LF_IndProp_exp__match Original_LF__DOT__Poly_LF_Poly_list.nil Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptyStr
  | MChar (x : T) : Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_list.cons x Original_LF__DOT__Poly_LF_Poly_list.nil) (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Char x)
  | MApp (s1 : Original_LF__DOT__Poly_LF_Poly_list T) (re1 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) 
         (s2 : Original_LF__DOT__Poly_LF_Poly_list T) (re2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
         (H1 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s1 re1)
         (H2 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s2 re2) :
         Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_app s1 s2) (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.App re1 re2)
  | MUnionL (s1 : Original_LF__DOT__Poly_LF_Poly_list T) (re1 re2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
            (H1 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s1 re1) :
            Original_LF__DOT__IndProp_LF_IndProp_exp__match s1 (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Union re1 re2)
  | MUnionR (s2 : Original_LF__DOT__Poly_LF_Poly_list T) (re1 re2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
            (H2 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s2 re2) :
            Original_LF__DOT__IndProp_LF_IndProp_exp__match s2 (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Union re1 re2)
  | MStar0 (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : 
           Original_LF__DOT__IndProp_LF_IndProp_exp__match Original_LF__DOT__Poly_LF_Poly_list.nil (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star re)
  | MStarApp (s1 s2 : Original_LF__DOT__Poly_LF_Poly_list T) (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
             (H1 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s1 re)
             (H2 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s2 (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star re)) :
             Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_app s1 s2) (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star re)

-- iff structure
structure iff (A B : Prop) : Prop where
  mp : A → B
  mpr : B → A

-- is_der definition
def Original_LF__DOT__IndProp_LF_IndProp_is__der (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp Ascii_ascii) (a : Ascii_ascii) (re' : Original_LF__DOT__IndProp_LF_IndProp_reg__exp Ascii_ascii) : Prop :=
  ∀ s : Original_LF__DOT__Poly_LF_Poly_list Ascii_ascii, 
    iff (Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_list.cons a s) re)
        (Original_LF__DOT__IndProp_LF_IndProp_exp__match s re')

-- derives definition
def Original_LF__DOT__IndProp_LF_IndProp_derives (d : Ascii_ascii → Original_LF__DOT__IndProp_LF_IndProp_reg__exp Ascii_ascii → Original_LF__DOT__IndProp_LF_IndProp_reg__exp Ascii_ascii) : Prop :=
  ∀ (a : Ascii_ascii) (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp Ascii_ascii), 
    Original_LF__DOT__IndProp_LF_IndProp_is__der re a (d a re)

-- False type (empty type)
inductive Original_False : Prop where

-- empty_nomatch_ne: axiom (Admitted in Original.v)
-- forall (a : ascii) s, (a :: s =~ EmptyStr) <-> False
axiom Original_LF__DOT__IndProp_LF_IndProp_empty__nomatch__ne : 
  ∀ (a : Ascii_ascii) (s : Original_LF__DOT__Poly_LF_Poly_list Ascii_ascii),
    iff (Original_LF__DOT__IndProp_LF_IndProp_exp__match 
           (Original_LF__DOT__Poly_LF_Poly_list.cons a s) 
           Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptyStr)
        Original_False
