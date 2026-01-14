-- Lean translation of Rocq definitions for re_opt_match and dependencies

-- Polymorphic list type (matching Original.LF_DOT_Poly.LF.Poly.list)
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

-- nil constructor as a function
def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

-- cons constructor as a function
def Original_LF__DOT__Poly_LF_Poly_cons (X : Type) (x : X) (l : Original_LF__DOT__Poly_LF_Poly_list X) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons x l

-- app function
def Original_LF__DOT__Poly_LF_Poly_app (X : Type) (l1 l2 : Original_LF__DOT__Poly_LF_Poly_list X) : Original_LF__DOT__Poly_LF_Poly_list X :=
  match l1 with
  | Original_LF__DOT__Poly_LF_Poly_list.nil => l2
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t => Original_LF__DOT__Poly_LF_Poly_list.cons h (Original_LF__DOT__Poly_LF_Poly_app X t l2)

-- Regular expression type (matching Original.LF_DOT_IndProp.LF.IndProp.reg_exp)
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

-- EmptyStr constructor as a function
def Original_LF__DOT__IndProp_LF_IndProp_EmptyStr (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptyStr

-- Char constructor as a function
def Original_LF__DOT__IndProp_LF_IndProp_Char (T : Type) (t : T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Char t

-- App constructor as a function
def Original_LF__DOT__IndProp_LF_IndProp_App (T : Type) (r1 r2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.App r1 r2

-- Union constructor as a function
def Original_LF__DOT__IndProp_LF_IndProp_Union (T : Type) (r1 r2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Union r1 r2

-- Star constructor as a function
def Original_LF__DOT__IndProp_LF_IndProp_Star (T : Type) (r : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star r

-- exp_match inductive proposition (matching Original.LF_DOT_IndProp.LF.IndProp.exp_match)
inductive Original_LF__DOT__IndProp_LF_IndProp_exp__match {T : Type} : Original_LF__DOT__Poly_LF_Poly_list T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Prop where
  | MEmpty : Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_list.nil) (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptyStr)
  | MChar (x : T) : Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_list.cons x Original_LF__DOT__Poly_LF_Poly_list.nil) (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Char x)
  | MApp (s1 : Original_LF__DOT__Poly_LF_Poly_list T) (re1 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) (s2 : Original_LF__DOT__Poly_LF_Poly_list T) (re2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
         (H1 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s1 re1)
         (H2 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s2 re2)
       : Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_app T s1 s2) (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.App re1 re2)
  | MUnionL (s1 : Original_LF__DOT__Poly_LF_Poly_list T) (re1 re2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
            (H1 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s1 re1)
          : Original_LF__DOT__IndProp_LF_IndProp_exp__match s1 (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Union re1 re2)
  | MUnionR (s2 : Original_LF__DOT__Poly_LF_Poly_list T) (re1 re2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
            (H2 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s2 re2)
          : Original_LF__DOT__IndProp_LF_IndProp_exp__match s2 (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Union re1 re2)
  | MStar0 (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_list.nil) (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star re)
  | MStarApp (s1 s2 : Original_LF__DOT__Poly_LF_Poly_list T) (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
             (H1 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s1 re)
             (H2 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s2 (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star re))
           : Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_app T s1 s2) (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star re)

-- re_opt function (matching Original.LF_DOT_AltAuto.LF.AltAuto.re_opt)
def Original_LF__DOT__AltAuto_LF_AltAuto_re__opt (T : Type) (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  match re with
  | Original_LF__DOT__IndProp_LF_IndProp_reg__exp.App _ Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptySet => 
      Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptySet
  | Original_LF__DOT__IndProp_LF_IndProp_reg__exp.App Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptyStr re2 => 
      Original_LF__DOT__AltAuto_LF_AltAuto_re__opt T re2
  | Original_LF__DOT__IndProp_LF_IndProp_reg__exp.App re1 Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptyStr => 
      Original_LF__DOT__AltAuto_LF_AltAuto_re__opt T re1
  | Original_LF__DOT__IndProp_LF_IndProp_reg__exp.App re1 re2 => 
      Original_LF__DOT__IndProp_LF_IndProp_reg__exp.App (Original_LF__DOT__AltAuto_LF_AltAuto_re__opt T re1) (Original_LF__DOT__AltAuto_LF_AltAuto_re__opt T re2)
  | Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Union Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptySet re2 => 
      Original_LF__DOT__AltAuto_LF_AltAuto_re__opt T re2
  | Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Union re1 Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptySet => 
      Original_LF__DOT__AltAuto_LF_AltAuto_re__opt T re1
  | Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Union re1 re2 => 
      Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Union (Original_LF__DOT__AltAuto_LF_AltAuto_re__opt T re1) (Original_LF__DOT__AltAuto_LF_AltAuto_re__opt T re2)
  | Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptySet => 
      Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptyStr
  | Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptyStr => 
      Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptyStr
  | Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star re => 
      Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star (Original_LF__DOT__AltAuto_LF_AltAuto_re__opt T re)
  | Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptySet => 
      Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptySet
  | Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptyStr => 
      Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptyStr
  | Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Char x => 
      Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Char x

-- re_opt_match is an axiom (Admitted in the original)
axiom Original_LF__DOT__AltAuto_LF_AltAuto_re__opt__match : ∀ (T : Type) (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) (s : Original_LF__DOT__Poly_LF_Poly_list T),
  Original_LF__DOT__IndProp_LF_IndProp_exp__match s re → Original_LF__DOT__IndProp_LF_IndProp_exp__match s (Original_LF__DOT__AltAuto_LF_AltAuto_re__opt T re)
