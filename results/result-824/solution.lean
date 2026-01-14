-- Lean translation for regex_match_correct and all dependencies

-- Standard bool for ascii (matches Stdlib.Init.Datatypes.bool)
inductive Stdlib_bool : Type where
  | true : Stdlib_bool
  | false : Stdlib_bool

-- Ascii type (8 booleans)
inductive Ascii_ascii : Type where
  | Ascii : Stdlib_bool → Stdlib_bool → Stdlib_bool → Stdlib_bool → 
            Stdlib_bool → Stdlib_bool → Stdlib_bool → Stdlib_bool → Ascii_ascii

-- Bool type (using our wrapper)
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- List type (matching Original.LF_DOT_Poly.LF.Poly.list)
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

def Original_LF__DOT__Poly_LF_Poly_cons (X : Type) (x : X) (xs : Original_LF__DOT__Poly_LF_Poly_list X) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons x xs

-- app function for list
def Original_LF__DOT__Poly_LF_Poly_app (X : Type) (l1 l2 : Original_LF__DOT__Poly_LF_Poly_list X) : Original_LF__DOT__Poly_LF_Poly_list X :=
  match l1 with
  | .nil => l2
  | .cons x xs => .cons x (Original_LF__DOT__Poly_LF_Poly_app X xs l2)

-- String is a type alias for list of ascii
def Original_LF__DOT__IndProp_LF_IndProp_string : Type := 
  Original_LF__DOT__Poly_LF_Poly_list Ascii_ascii

-- Regular expression type
inductive Original_LF__DOT__IndProp_LF_IndProp_reg__exp (T : Type) : Type where
  | EmptySet : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | EmptyStr : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Char : T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | App : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Union : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Star : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T

-- Constructor exports
def Original_LF__DOT__IndProp_LF_IndProp_EmptyStr (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptyStr

def Original_LF__DOT__IndProp_LF_IndProp_Char (T : Type) (t : T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Char t

def Original_LF__DOT__IndProp_LF_IndProp_App (T : Type) (r1 r2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.App r1 r2

def Original_LF__DOT__IndProp_LF_IndProp_Union (T : Type) (r1 r2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Union r1 r2

def Original_LF__DOT__IndProp_LF_IndProp_Star (T : Type) (r : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star r

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

-- reflect type
inductive Original_LF__DOT__IndProp_LF_IndProp_reflect (P : Prop) : Original_LF__DOT__Basics_LF_Basics_bool → Prop where
  | ReflectT (H : P) : Original_LF__DOT__IndProp_LF_IndProp_reflect P Original_LF__DOT__Basics_LF_Basics_bool.true
  | ReflectF (H : ¬P) : Original_LF__DOT__IndProp_LF_IndProp_reflect P Original_LF__DOT__Basics_LF_Basics_bool.false

-- matches_regex definition
def Original_LF__DOT__IndProp_LF_IndProp_matches__regex 
    (m : Original_LF__DOT__Poly_LF_Poly_list Ascii_ascii → Original_LF__DOT__IndProp_LF_IndProp_reg__exp Ascii_ascii → Original_LF__DOT__Basics_LF_Basics_bool) : Prop :=
  ∀ (s : Original_LF__DOT__Poly_LF_Poly_list Ascii_ascii) (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp Ascii_ascii),
    Original_LF__DOT__IndProp_LF_IndProp_reflect (Original_LF__DOT__IndProp_LF_IndProp_exp__match s re) (m s re)

-- regex_match is Admitted in Rocq, so we use an axiom
axiom Original_LF__DOT__IndProp_LF_IndProp_regex__match : 
  Original_LF__DOT__Poly_LF_Poly_list Ascii_ascii → 
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp Ascii_ascii → 
  Original_LF__DOT__Basics_LF_Basics_bool

-- regex_match_correct is Admitted in Rocq, so we use an axiom
axiom Original_LF__DOT__IndProp_LF_IndProp_regex__match__correct : 
  Original_LF__DOT__IndProp_LF_IndProp_matches__regex Original_LF__DOT__IndProp_LF_IndProp_regex__match

-- refl_matches_eps definition: forall re, reflect ([] =~ re) (m re)
def Original_LF__DOT__IndProp_LF_IndProp_refl__matches__eps 
    (m : Original_LF__DOT__IndProp_LF_IndProp_reg__exp Ascii_ascii → Original_LF__DOT__Basics_LF_Basics_bool) : Prop :=
  ∀ (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp Ascii_ascii),
    Original_LF__DOT__IndProp_LF_IndProp_reflect 
      (Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_nil Ascii_ascii) re) 
      (m re)

-- match_eps is Admitted in Rocq, so we use an axiom
axiom Original_LF__DOT__IndProp_LF_IndProp_match__eps : 
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp Ascii_ascii → 
  Original_LF__DOT__Basics_LF_Basics_bool

-- match_eps_refl is Admitted in Rocq, so we use an axiom
axiom Original_LF__DOT__IndProp_LF_IndProp_match__eps__refl : 
  Original_LF__DOT__IndProp_LF_IndProp_refl__matches__eps Original_LF__DOT__IndProp_LF_IndProp_match__eps
