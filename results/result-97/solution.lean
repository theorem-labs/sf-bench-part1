-- Lean translation for re_opt_match and all dependencies

-- Standard bool (matches Stdlib.Init.Datatypes.bool)
-- Named to match what Rocq isomorphism proofs expect
inductive mybool : Type where
  | true : mybool
  | false : mybool

def mybool_true : mybool := mybool.true
def mybool_false : mybool := mybool.false

-- Standard bool for Stdlib (needed for Ascii)
abbrev Stdlib_bool := mybool
abbrev Stdlib_bool_true := mybool_true
abbrev Stdlib_bool_false := mybool_false

-- Ascii type (8 booleans)
inductive Ascii_ascii : Type where
  | Ascii : mybool → mybool → mybool → mybool → mybool → mybool → mybool → mybool → Ascii_ascii

def Ascii_ascii_Ascii (b0 b1 b2 b3 b4 b5 b6 b7 : mybool) : Ascii_ascii :=
  Ascii_ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7

-- Alias with expected name pattern
def Ascii_Ascii := Ascii_ascii_Ascii

-- List type (matching Original.LF_DOT_Poly.LF.Poly.list)
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

def Original_LF__DOT__Poly_LF_Poly_list_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

def Original_LF__DOT__Poly_LF_Poly_list_cons (X : Type) (x : X) (xs : Original_LF__DOT__Poly_LF_Poly_list X) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons x xs

-- Aliases with alternate naming (for isomorphism files)
abbrev Original_LF__DOT__Poly_LF_Poly_nil := Original_LF__DOT__Poly_LF_Poly_list_nil
abbrev Original_LF__DOT__Poly_LF_Poly_cons := Original_LF__DOT__Poly_LF_Poly_list_cons

-- app function for list
def Original_LF__DOT__Poly_LF_Poly_app (X : Type) (l1 l2 : Original_LF__DOT__Poly_LF_Poly_list X) : Original_LF__DOT__Poly_LF_Poly_list X :=
  match l1 with
  | .nil => l2
  | .cons x xs => .cons x (Original_LF__DOT__Poly_LF_Poly_app X xs l2)

-- Regular expression type
inductive Original_LF__DOT__IndProp_LF_IndProp_reg__exp (T : Type) : Type where
  | EmptySet : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | EmptyStr : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Char : T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | App : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Union : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Star : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T

-- Constructor aliases for reg_exp
def Original_LF__DOT__IndProp_LF_IndProp_reg__exp_EmptySet (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptySet

def Original_LF__DOT__IndProp_LF_IndProp_reg__exp_EmptyStr (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptyStr

def Original_LF__DOT__IndProp_LF_IndProp_reg__exp_Char (T : Type) (t : T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Char t

def Original_LF__DOT__IndProp_LF_IndProp_reg__exp_App (T : Type) (r1 r2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.App r1 r2

def Original_LF__DOT__IndProp_LF_IndProp_reg__exp_Union (T : Type) (r1 r2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Union r1 r2

def Original_LF__DOT__IndProp_LF_IndProp_reg__exp_Star (T : Type) (r : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star r

-- Aliases with alternate naming (for isomorphism files)
abbrev Original_LF__DOT__IndProp_LF_IndProp_EmptySet := Original_LF__DOT__IndProp_LF_IndProp_reg__exp_EmptySet
abbrev Original_LF__DOT__IndProp_LF_IndProp_EmptyStr := Original_LF__DOT__IndProp_LF_IndProp_reg__exp_EmptyStr
abbrev Original_LF__DOT__IndProp_LF_IndProp_Char := Original_LF__DOT__IndProp_LF_IndProp_reg__exp_Char
abbrev Original_LF__DOT__IndProp_LF_IndProp_App := Original_LF__DOT__IndProp_LF_IndProp_reg__exp_App
abbrev Original_LF__DOT__IndProp_LF_IndProp_Union := Original_LF__DOT__IndProp_LF_IndProp_reg__exp_Union
abbrev Original_LF__DOT__IndProp_LF_IndProp_Star := Original_LF__DOT__IndProp_LF_IndProp_reg__exp_Star

-- exp_match inductive (propositional type)
inductive Original_LF__DOT__IndProp_LF_IndProp_exp__match {T : Type} : Original_LF__DOT__Poly_LF_Poly_list T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Prop where
  | MEmpty : Original_LF__DOT__IndProp_LF_IndProp_exp__match Original_LF__DOT__Poly_LF_Poly_list.nil Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptyStr
  | MChar (x : T) : Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_list.cons x Original_LF__DOT__Poly_LF_Poly_list.nil) (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Char x)
  | MApp (s1 : Original_LF__DOT__Poly_LF_Poly_list T) (re1 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) 
         (s2 : Original_LF__DOT__Poly_LF_Poly_list T) (re2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
         (H1 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s1 re1)
         (H2 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s2 re2)
       : Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_app T s1 s2) (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.App re1 re2)
  | MUnionL (s1 : Original_LF__DOT__Poly_LF_Poly_list T) (re1 re2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
            (H1 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s1 re1)
          : Original_LF__DOT__IndProp_LF_IndProp_exp__match s1 (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Union re1 re2)
  | MUnionR (s2 : Original_LF__DOT__Poly_LF_Poly_list T) (re1 re2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
            (H2 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s2 re2)
          : Original_LF__DOT__IndProp_LF_IndProp_exp__match s2 (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Union re1 re2)
  | MStar0 (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) 
         : Original_LF__DOT__IndProp_LF_IndProp_exp__match Original_LF__DOT__Poly_LF_Poly_list.nil (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star re)
  | MStarApp (s1 s2 : Original_LF__DOT__Poly_LF_Poly_list T) (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
             (H1 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s1 re)
             (H2 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s2 (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star re))
           : Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_app T s1 s2) (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star re)

-- Constructor aliases for exp_match
def Original_LF__DOT__IndProp_LF_IndProp_exp__match_MEmpty (T : Type) : @Original_LF__DOT__IndProp_LF_IndProp_exp__match T Original_LF__DOT__Poly_LF_Poly_list.nil Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptyStr :=
  Original_LF__DOT__IndProp_LF_IndProp_exp__match.MEmpty

def Original_LF__DOT__IndProp_LF_IndProp_exp__match_MChar (T : Type) (x : T) : @Original_LF__DOT__IndProp_LF_IndProp_exp__match T (Original_LF__DOT__Poly_LF_Poly_list.cons x Original_LF__DOT__Poly_LF_Poly_list.nil) (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Char x) :=
  Original_LF__DOT__IndProp_LF_IndProp_exp__match.MChar x

def Original_LF__DOT__IndProp_LF_IndProp_exp__match_MApp (T : Type) 
    (s1 : Original_LF__DOT__Poly_LF_Poly_list T) (re1 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) 
    (s2 : Original_LF__DOT__Poly_LF_Poly_list T) (re2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
    (H1 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s1 re1)
    (H2 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s2 re2)
  : @Original_LF__DOT__IndProp_LF_IndProp_exp__match T (Original_LF__DOT__Poly_LF_Poly_app T s1 s2) (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.App re1 re2) :=
  Original_LF__DOT__IndProp_LF_IndProp_exp__match.MApp s1 re1 s2 re2 H1 H2

def Original_LF__DOT__IndProp_LF_IndProp_exp__match_MUnionL (T : Type) 
    (s1 : Original_LF__DOT__Poly_LF_Poly_list T) (re1 re2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
    (H1 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s1 re1)
  : @Original_LF__DOT__IndProp_LF_IndProp_exp__match T s1 (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Union re1 re2) :=
  Original_LF__DOT__IndProp_LF_IndProp_exp__match.MUnionL s1 re1 re2 H1

def Original_LF__DOT__IndProp_LF_IndProp_exp__match_MUnionR (T : Type) 
    (s2 : Original_LF__DOT__Poly_LF_Poly_list T) (re1 re2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
    (H2 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s2 re2)
  : @Original_LF__DOT__IndProp_LF_IndProp_exp__match T s2 (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Union re1 re2) :=
  Original_LF__DOT__IndProp_LF_IndProp_exp__match.MUnionR s2 re1 re2 H2

def Original_LF__DOT__IndProp_LF_IndProp_exp__match_MStar0 (T : Type) 
    (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
  : @Original_LF__DOT__IndProp_LF_IndProp_exp__match T Original_LF__DOT__Poly_LF_Poly_list.nil (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star re) :=
  Original_LF__DOT__IndProp_LF_IndProp_exp__match.MStar0 re

def Original_LF__DOT__IndProp_LF_IndProp_exp__match_MStarApp (T : Type) 
    (s1 s2 : Original_LF__DOT__Poly_LF_Poly_list T) (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
    (H1 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s1 re)
    (H2 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s2 (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star re))
  : @Original_LF__DOT__IndProp_LF_IndProp_exp__match T (Original_LF__DOT__Poly_LF_Poly_app T s1 s2) (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star re) :=
  Original_LF__DOT__IndProp_LF_IndProp_exp__match.MStarApp s1 s2 re H1 H2

-- re_opt function (translation of Original.LF_DOT_AltAuto.LF.AltAuto.re_opt)
def Original_LF__DOT__AltAuto_LF_AltAuto_re__opt {T : Type} (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  match re with
  | .App _ .EmptySet => .EmptySet
  | .App .EmptyStr re2 => Original_LF__DOT__AltAuto_LF_AltAuto_re__opt re2
  | .App re1 .EmptyStr => Original_LF__DOT__AltAuto_LF_AltAuto_re__opt re1
  | .App re1 re2 => .App (Original_LF__DOT__AltAuto_LF_AltAuto_re__opt re1) (Original_LF__DOT__AltAuto_LF_AltAuto_re__opt re2)
  | .Union .EmptySet re2 => Original_LF__DOT__AltAuto_LF_AltAuto_re__opt re2
  | .Union re1 .EmptySet => Original_LF__DOT__AltAuto_LF_AltAuto_re__opt re1
  | .Union re1 re2 => .Union (Original_LF__DOT__AltAuto_LF_AltAuto_re__opt re1) (Original_LF__DOT__AltAuto_LF_AltAuto_re__opt re2)
  | .Star .EmptySet => .EmptyStr
  | .Star .EmptyStr => .EmptyStr
  | .Star re' => .Star (Original_LF__DOT__AltAuto_LF_AltAuto_re__opt re')
  | .EmptySet => .EmptySet
  | .EmptyStr => .EmptyStr
  | .Char x => .Char x

-- re_opt_match is Admitted in Rocq, so we use an axiom
axiom Original_LF__DOT__AltAuto_LF_AltAuto_re__opt__match : ∀ (T : Type) (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) (s : Original_LF__DOT__Poly_LF_Poly_list T),
  Original_LF__DOT__IndProp_LF_IndProp_exp__match s re → Original_LF__DOT__IndProp_LF_IndProp_exp__match s (Original_LF__DOT__AltAuto_LF_AltAuto_re__opt re)
