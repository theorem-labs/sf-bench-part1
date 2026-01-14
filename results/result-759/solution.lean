-- Lean translation for napp_star and its dependencies

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

-- Polymorphic list type
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

-- List constructors
def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

def Original_LF__DOT__Poly_LF_Poly_cons (X : Type) : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons

-- List append function
def Original_LF__DOT__Poly_LF_Poly_app (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X
  | Original_LF__DOT__Poly_LF_Poly_list.nil, l2 => l2
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t, l2 => Original_LF__DOT__Poly_LF_Poly_list.cons h (Original_LF__DOT__Poly_LF_Poly_app X t l2)

-- Regular expression type
inductive Original_LF__DOT__IndProp_LF_IndProp_reg__exp (T : Type) : Type where
  | EmptySet : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | EmptyStr : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Char : T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | App : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Union : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Star : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T

-- reg_exp constructors
def Original_LF__DOT__IndProp_LF_IndProp_EmptyStr (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptyStr

def Original_LF__DOT__IndProp_LF_IndProp_Char (T : Type) : T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Char

def Original_LF__DOT__IndProp_LF_IndProp_App (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.App

def Original_LF__DOT__IndProp_LF_IndProp_Union (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Union

def Original_LF__DOT__IndProp_LF_IndProp_Star (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star

-- exp_match inductive type (string matches regular expression)
inductive Original_LF__DOT__IndProp_LF_IndProp_exp__match {T : Type} : Original_LF__DOT__Poly_LF_Poly_list T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Prop where
  | MEmpty : Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_list.nil) Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptyStr
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
  | MStar0 (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
    : Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_list.nil) (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star re)
  | MStarApp (s1 s2 : Original_LF__DOT__Poly_LF_Poly_list T) (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
      (H1 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s1 re)
      (H2 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s2 (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star re))
    : Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_app T s1 s2) (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star re)

-- The napp function (repeat append)
def Original_LF__DOT__IndProp_LF_IndProp_Pumping_napp (X : Type) : nat → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X
  | nat.O, _ => Original_LF__DOT__Poly_LF_Poly_list.nil
  | nat.S n', l => Original_LF__DOT__Poly_LF_Poly_app X l (Original_LF__DOT__IndProp_LF_IndProp_Pumping_napp X n' l)

-- The napp_star axiom (it's Admitted in the original)
axiom Original_LF__DOT__IndProp_LF_IndProp_Pumping_napp__star : ∀ (T : Type) (m : nat) (s1 s2 : Original_LF__DOT__Poly_LF_Poly_list T) (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T),
  Original_LF__DOT__IndProp_LF_IndProp_exp__match s1 re →
  Original_LF__DOT__IndProp_LF_IndProp_exp__match s2 (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star re) →
  Original_LF__DOT__IndProp_LF_IndProp_exp__match 
    (Original_LF__DOT__Poly_LF_Poly_app T (Original_LF__DOT__IndProp_LF_IndProp_Pumping_napp T m s1) s2)
    (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star re)
