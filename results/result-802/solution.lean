/-
  Lean translation for star_ne and all dependencies
  
  Required definitions for the isomorphism:
  - Ascii_ascii
  - Original_LF__DOT__Poly_LF_Poly_list (polymorphic list)
  - Original_LF__DOT__Poly_LF_Poly_nil, cons, app
  - Original_LF__DOT__IndProp_LF_IndProp_reg__exp
  - Original_LF__DOT__IndProp_LF_IndProp_Star, Union, App, Char, EmptyStr
  - Original_LF__DOT__IndProp_LF_IndProp_exp__match
  - Corelib_Init_Logic_eq
  - and, ex, iff
  - True
  - star_ne (the axiom)
-/

set_option autoImplicit false

-- Bool type for Ascii
inductive Stdlib_bool : Type where
  | true : Stdlib_bool
  | false : Stdlib_bool

-- True type (will become SProp in Rocq)
-- Define using double guillemets - try direct abbreviation
def myTrue : Prop := _root_.True
def myTrue_intro : myTrue := _root_.True.intro

-- Equality in Prop (for Type)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl : ∀ (a : A), Corelib_Init_Logic_eq a a

-- Equality in Prop (for Prop - needed by checker)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl : ∀ (a : A), Corelib_Init_Logic_eq_Prop a a

-- Ascii type (8 booleans)
inductive Ascii_ascii : Type where
  | Ascii : Stdlib_bool → Stdlib_bool → Stdlib_bool → Stdlib_bool → 
            Stdlib_bool → Stdlib_bool → Stdlib_bool → Stdlib_bool → Ascii_ascii

-- Polymorphic list type matching Original.LF_DOT_Poly.LF.Poly.list
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

-- List constructors as explicit definitions
def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

def Original_LF__DOT__Poly_LF_Poly_cons (X : Type) : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons

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

-- Constructor exports for reg_exp
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

-- iff type (matching Coq iff)
structure iff (P Q : Prop) : Prop where
  mp : P → Q
  mpr : Q → P

-- and type (matching Coq and)
structure and (P Q : Prop) : Prop where
  intro ::
  left : P
  right : Q

-- ex type (matching Coq ex)
inductive ex {A : Type} (P : A → Prop) : Prop where
  | intro (w : A) (H : P w) : ex P

-- star_ne is an Admitted axiom in Original.v
-- star_ne : forall (a : ascii) s re,
--   a :: s =~ Star re <->
--   exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re /\ s1 =~ Star re.
axiom Original_LF__DOT__IndProp_LF_IndProp_star__ne : 
  ∀ (a : Ascii_ascii) (s : Original_LF__DOT__Poly_LF_Poly_list Ascii_ascii) (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp Ascii_ascii),
    iff 
      (@Original_LF__DOT__IndProp_LF_IndProp_exp__match Ascii_ascii 
        (Original_LF__DOT__Poly_LF_Poly_list.cons a s) 
        (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star re))
      (ex (fun s0 : Original_LF__DOT__Poly_LF_Poly_list Ascii_ascii =>
        ex (fun s1 : Original_LF__DOT__Poly_LF_Poly_list Ascii_ascii =>
          and 
            (Corelib_Init_Logic_eq s (Original_LF__DOT__Poly_LF_Poly_app Ascii_ascii s0 s1))
            (and 
              (@Original_LF__DOT__IndProp_LF_IndProp_exp__match Ascii_ascii 
                (Original_LF__DOT__Poly_LF_Poly_list.cons a s0) re)
              (@Original_LF__DOT__IndProp_LF_IndProp_exp__match Ascii_ascii s1 
                (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star re))))))
