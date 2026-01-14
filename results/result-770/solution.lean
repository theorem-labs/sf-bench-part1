/-
  Lean translation for MStar' and all dependencies
  
  Required definitions:
  - Original.LF_DOT_Poly.LF.Poly.list
  - Original.LF_DOT_Poly.LF.Poly.nil
  - Original.LF_DOT_Poly.LF.Poly.cons
  - Original.LF_DOT_Poly.LF.Poly.app
  - Original.LF_DOT_Poly.LF.Poly.fold
  - Original.LF_DOT_IndProp.LF.IndProp.reg_exp
  - Original.LF_DOT_IndProp.LF.IndProp.EmptySet
  - Original.LF_DOT_IndProp.LF.IndProp.EmptyStr
  - Original.LF_DOT_IndProp.LF.IndProp.Char
  - Original.LF_DOT_IndProp.LF.IndProp.App
  - Original.LF_DOT_IndProp.LF.IndProp.Union
  - Original.LF_DOT_IndProp.LF.IndProp.Star
  - Original.LF_DOT_IndProp.LF.IndProp.exp_match
  - Original.LF_DOT_Logic.LF.Logic.In
  - Original.False
  - Original.LF_DOT_IndProp.LF.IndProp.MStar' (axiom)
-/

set_option autoImplicit false

-- MyFalse: empty inductive type for False
inductive MyFalse : Prop where

-- Original.False
abbrev Original_False := MyFalse

-- Polymorphic list type matching Original.LF_DOT_Poly.LF.Poly.list
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

-- nil constructor
def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

-- cons constructor
def Original_LF__DOT__Poly_LF_Poly_cons (X : Type) : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons

-- app function
def Original_LF__DOT__Poly_LF_Poly_app (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X
  | .nil, l2 => l2
  | .cons h t, l2 => .cons h (Original_LF__DOT__Poly_LF_Poly_app X t l2)

-- fold function
def Original_LF__DOT__Poly_LF_Poly_fold (X Y : Type) (f : X → Y → Y) : Original_LF__DOT__Poly_LF_Poly_list X → Y → Y
  | .nil, b => b
  | .cons h t, b => f h (Original_LF__DOT__Poly_LF_Poly_fold X Y f t b)

-- In predicate: checks if x is in the list
def Original_LF__DOT__Logic_LF_Logic_In {A : Type} (x : A) (l : Original_LF__DOT__Poly_LF_Poly_list A) : Prop :=
  match l with
  | .nil => Original_False
  | .cons x' l' => x' = x ∨ Original_LF__DOT__Logic_LF_Logic_In x l'

-- Regular expression type
inductive Original_LF__DOT__IndProp_LF_IndProp_reg__exp (T : Type) : Type where
  | EmptySet : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | EmptyStr : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Char : T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | App : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Union : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Star : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T

-- Constructor definitions for reg_exp
def Original_LF__DOT__IndProp_LF_IndProp_EmptySet (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  .EmptySet

def Original_LF__DOT__IndProp_LF_IndProp_EmptyStr (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  .EmptyStr

def Original_LF__DOT__IndProp_LF_IndProp_Char (T : Type) : T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  .Char

def Original_LF__DOT__IndProp_LF_IndProp_App (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  .App

def Original_LF__DOT__IndProp_LF_IndProp_Union (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  .Union

def Original_LF__DOT__IndProp_LF_IndProp_Star (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  .Star

-- exp_match inductive type (s =~ re)
inductive Original_LF__DOT__IndProp_LF_IndProp_exp__match {T : Type} : 
    Original_LF__DOT__Poly_LF_Poly_list T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Prop where
  | MEmpty : Original_LF__DOT__IndProp_LF_IndProp_exp__match .nil .EmptyStr
  | MChar (x : T) : Original_LF__DOT__IndProp_LF_IndProp_exp__match (.cons x .nil) (.Char x)
  | MApp (s1 : Original_LF__DOT__Poly_LF_Poly_list T) (re1 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
         (s2 : Original_LF__DOT__Poly_LF_Poly_list T) (re2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
         (H1 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s1 re1)
         (H2 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s2 re2) :
         Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_app T s1 s2) (.App re1 re2)
  | MUnionL (s1 : Original_LF__DOT__Poly_LF_Poly_list T) (re1 re2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
            (H1 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s1 re1) :
            Original_LF__DOT__IndProp_LF_IndProp_exp__match s1 (.Union re1 re2)
  | MUnionR (s2 : Original_LF__DOT__Poly_LF_Poly_list T) (re1 re2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
            (H2 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s2 re2) :
            Original_LF__DOT__IndProp_LF_IndProp_exp__match s2 (.Union re1 re2)
  | MStar0 (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) :
           Original_LF__DOT__IndProp_LF_IndProp_exp__match .nil (.Star re)
  | MStarApp (s1 s2 : Original_LF__DOT__Poly_LF_Poly_list T) (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
             (H1 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s1 re)
             (H2 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s2 (.Star re)) :
             Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_app T s1 s2) (.Star re)

-- re_chars: extract characters from regex
def Original_LF__DOT__IndProp_LF_IndProp_re__chars (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__Poly_LF_Poly_list T
  | .EmptySet => .nil
  | .EmptyStr => .nil
  | .Char x => .cons x .nil
  | .App re1 re2 => Original_LF__DOT__Poly_LF_Poly_app T (Original_LF__DOT__IndProp_LF_IndProp_re__chars T re1) (Original_LF__DOT__IndProp_LF_IndProp_re__chars T re2)
  | .Union re1 re2 => Original_LF__DOT__Poly_LF_Poly_app T (Original_LF__DOT__IndProp_LF_IndProp_re__chars T re1) (Original_LF__DOT__IndProp_LF_IndProp_re__chars T re2)
  | .Star re => Original_LF__DOT__IndProp_LF_IndProp_re__chars T re

-- in_re_match is Admitted in Original.v - we axiomatize it
axiom Original_LF__DOT__IndProp_LF_IndProp_in__re__match :
  ∀ (T : Type) (s : Original_LF__DOT__Poly_LF_Poly_list T) (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) (x : T),
    Original_LF__DOT__IndProp_LF_IndProp_exp__match s re →
    Original_LF__DOT__Logic_LF_Logic_In x s →
    Original_LF__DOT__Logic_LF_Logic_In x (Original_LF__DOT__IndProp_LF_IndProp_re__chars T re)

-- MStar' is an admitted axiom in Original.v
-- MStar' : forall T (ss : list (list T)) (re : reg_exp T),
--   (forall s, In s ss -> s =~ re) ->
--   fold app ss [] =~ Star re.
axiom Original_LF__DOT__IndProp_LF_IndProp_MStar' : 
  ∀ (T : Type) 
    (ss : Original_LF__DOT__Poly_LF_Poly_list (Original_LF__DOT__Poly_LF_Poly_list T)) 
    (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T),
    (∀ (s : Original_LF__DOT__Poly_LF_Poly_list T), 
       Original_LF__DOT__Logic_LF_Logic_In s ss → 
       Original_LF__DOT__IndProp_LF_IndProp_exp__match s re) →
    Original_LF__DOT__IndProp_LF_IndProp_exp__match 
      (Original_LF__DOT__Poly_LF_Poly_fold 
         (Original_LF__DOT__Poly_LF_Poly_list T)
         (Original_LF__DOT__Poly_LF_Poly_list T)
         (fun x y => Original_LF__DOT__Poly_LF_Poly_app T x y) 
         ss 
         (Original_LF__DOT__Poly_LF_Poly_nil T))
      (.Star re)
