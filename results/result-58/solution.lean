-- Comprehensive Lean translation for all required isomorphisms
set_option linter.all false
set_option autoImplicit false

-- ============================================================
-- Basic Types
-- ============================================================

-- Custom bool to avoid Lean stdlib issues
inductive Stdlib_bool : Type where
  | true : Stdlib_bool
  | false : Stdlib_bool

def Stdlib_bool_true := Stdlib_bool.true
def Stdlib_bool_false := Stdlib_bool.false

-- True type (will become SProp in Rocq)
def myTrue : Prop := _root_.True
def myTrue_intro : myTrue := _root_.True.intro

-- Equality in Prop (for Type arguments - will become SProp in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl a

-- Equality in Prop for Prop arguments
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

def Corelib_Init_Logic_eq_Prop_refl {A : Prop} (a : A) : Corelib_Init_Logic_eq_Prop a a :=
  Corelib_Init_Logic_eq_Prop.refl a

-- Custom nat
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Addition on nat
def Nat_add : nat → nat → nat
  | nat.O, m => m
  | nat.S p, m => nat.S (Nat_add p m)

-- Multiplication on nat
def Nat_mul : nat → nat → nat
  | nat.O, _ => nat.O
  | nat.S n, m => Nat_add (Nat_mul n m) m

-- Nat equality
def Nat_eqb : nat → nat → Stdlib_bool
  | nat.O, nat.O => Stdlib_bool.true
  | nat.S n, nat.S m => Nat_eqb n m
  | _, _ => Stdlib_bool.false

-- Nat less-than-or-equal
def Nat_leb : nat → nat → Stdlib_bool
  | nat.O, _ => Stdlib_bool.true
  | nat.S _, nat.O => Stdlib_bool.false
  | nat.S n, nat.S m => Nat_leb n m

-- le and lt as Props
-- Inductive less-than-or-equal
inductive nat_le : nat → nat → Prop where
  | le_n (n : nat) : nat_le n n
  | le_S (n m : nat) : nat_le n m → nat_le n (nat.S m)

def le (n m : nat) : Prop := nat_le n m
def lt (n m : nat) : Prop := le (nat.S n) m

-- Bool operations
def negb : Stdlib_bool → Stdlib_bool
  | Stdlib_bool.true => Stdlib_bool.false
  | Stdlib_bool.false => Stdlib_bool.true

def andb : Stdlib_bool → Stdlib_bool → Stdlib_bool
  | Stdlib_bool.true, b => b
  | Stdlib_bool.false, _ => Stdlib_bool.false

def orb : Stdlib_bool → Stdlib_bool → Stdlib_bool
  | Stdlib_bool.true, _ => Stdlib_bool.true
  | Stdlib_bool.false, b => b

def Bool_eqb : Stdlib_bool → Stdlib_bool → Stdlib_bool
  | Stdlib_bool.true, Stdlib_bool.true => Stdlib_bool.true
  | Stdlib_bool.false, Stdlib_bool.false => Stdlib_bool.true
  | _, _ => Stdlib_bool.false

-- ============================================================
-- Ascii and String types
-- ============================================================

inductive Ascii_ascii : Type where
  | Ascii : Stdlib_bool → Stdlib_bool → Stdlib_bool → Stdlib_bool →
            Stdlib_bool → Stdlib_bool → Stdlib_bool → Stdlib_bool → Ascii_ascii

def Ascii_Ascii := Ascii_ascii.Ascii

def Ascii_eqb : Ascii_ascii → Ascii_ascii → Stdlib_bool
  | Ascii_ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7, Ascii_ascii.Ascii c0 c1 c2 c3 c4 c5 c6 c7 =>
    andb (Bool_eqb b0 c0) (andb (Bool_eqb b1 c1) (andb (Bool_eqb b2 c2) (andb (Bool_eqb b3 c3)
      (andb (Bool_eqb b4 c4) (andb (Bool_eqb b5 c5) (andb (Bool_eqb b6 c6) (Bool_eqb b7 c7)))))))

inductive String_string : Type where
  | EmptyString : String_string
  | String : Ascii_ascii → String_string → String_string

def String_EmptyString := String_string.EmptyString
def String_String := String_string.String

def String_eqb : String_string → String_string → Stdlib_bool
  | String_string.EmptyString, String_string.EmptyString => Stdlib_bool.true
  | String_string.String a1 s1, String_string.String a2 s2 => andb (Ascii_eqb a1 a2) (String_eqb s1 s2)
  | _, _ => Stdlib_bool.false

-- ============================================================
-- Logical types
-- ============================================================

-- and type
structure and (P Q : Prop) : Prop where
  intro ::
  left : P
  right : Q

-- or type as a structure with eliminator
structure or (A B : Prop) : Prop where
  intro ::
  elim : ∀ C : Prop, (A → C) → (B → C) → C

def or_inl {A B : Prop} (a : A) : or A B := ⟨fun _ f _ => f a⟩
def or_inr {A B : Prop} (b : B) : or A B := ⟨fun _ _ g => g b⟩

-- iff type
structure iff (P Q : Prop) : Prop where
  mk ::
  mp : P → Q
  mpr : Q → P

-- ex type
inductive ex {A : Type} (P : A → Prop) : Prop where
  | intro (w : A) (H : P w) : ex P

-- prod type
structure prod (A B : Type) : Type where
  mk ::
  fst : A
  snd : B

def prod_pair (A B : Type) (a : A) (b : B) : prod A B := ⟨a, b⟩

-- ============================================================
-- Original.LF_DOT_Basics definitions
-- ============================================================

-- Bool type (matching LF.Basics.bool)
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- negb function
def Original_LF__DOT__Basics_LF_Basics_negb (b : Original_LF__DOT__Basics_LF_Basics_bool) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match b with
  | Original_LF__DOT__Basics_LF_Basics_bool.true => Original_LF__DOT__Basics_LF_Basics_bool.false
  | Original_LF__DOT__Basics_LF_Basics_bool.false => Original_LF__DOT__Basics_LF_Basics_bool.true

-- even function
def Original_LF__DOT__Basics_LF_Basics_even : nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O => Original_LF__DOT__Basics_LF_Basics_bool.true
  | nat.S nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S (nat.S n') => Original_LF__DOT__Basics_LF_Basics_even n'

-- odd function = negb (even n)
def Original_LF__DOT__Basics_LF_Basics_odd (n : nat) : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_negb (Original_LF__DOT__Basics_LF_Basics_even n)

-- eqb function
def Original_LF__DOT__Basics_LF_Basics_eqb : nat → nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.true
  | nat.S n, nat.S m => Original_LF__DOT__Basics_LF_Basics_eqb n m
  | _, _ => Original_LF__DOT__Basics_LF_Basics_bool.false

-- leb function (less than or equal)
def Original_LF__DOT__Basics_LF_Basics_leb : nat → nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O, _ => Original_LF__DOT__Basics_LF_Basics_bool.true
  | nat.S _, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S n, nat.S m => Original_LF__DOT__Basics_LF_Basics_leb n m

-- plus function from LF.Basics
def Original_LF__DOT__Basics_LF_Basics_plus : nat → nat → nat
  | nat.O, m => m
  | nat.S n', m => nat.S (Original_LF__DOT__Basics_LF_Basics_plus n' m)

-- ltb function
def Original_LF__DOT__Basics_LF_Basics_ltb : nat → nat → Original_LF__DOT__Basics_LF_Basics_bool
  | _, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.O, nat.S _ => Original_LF__DOT__Basics_LF_Basics_bool.true
  | nat.S n', nat.S m' => Original_LF__DOT__Basics_LF_Basics_ltb n' m'

-- Letter type: A, B, C, D, F
inductive Original_LF__DOT__Basics_LF_Basics_letter : Type where
  | A : Original_LF__DOT__Basics_LF_Basics_letter
  | B : Original_LF__DOT__Basics_LF_Basics_letter
  | C : Original_LF__DOT__Basics_LF_Basics_letter
  | D : Original_LF__DOT__Basics_LF_Basics_letter
  | F : Original_LF__DOT__Basics_LF_Basics_letter

def Original_LF__DOT__Basics_LF_Basics_A : Original_LF__DOT__Basics_LF_Basics_letter := Original_LF__DOT__Basics_LF_Basics_letter.A
def Original_LF__DOT__Basics_LF_Basics_B : Original_LF__DOT__Basics_LF_Basics_letter := Original_LF__DOT__Basics_LF_Basics_letter.B
def Original_LF__DOT__Basics_LF_Basics_C : Original_LF__DOT__Basics_LF_Basics_letter := Original_LF__DOT__Basics_LF_Basics_letter.C
def Original_LF__DOT__Basics_LF_Basics_D : Original_LF__DOT__Basics_LF_Basics_letter := Original_LF__DOT__Basics_LF_Basics_letter.D
def Original_LF__DOT__Basics_LF_Basics_F : Original_LF__DOT__Basics_LF_Basics_letter := Original_LF__DOT__Basics_LF_Basics_letter.F

-- Modifier type: Plus, Natural, Minus
inductive Original_LF__DOT__Basics_LF_Basics_modifier : Type where
  | Plus : Original_LF__DOT__Basics_LF_Basics_modifier
  | Natural : Original_LF__DOT__Basics_LF_Basics_modifier
  | Minus : Original_LF__DOT__Basics_LF_Basics_modifier

def Original_LF__DOT__Basics_LF_Basics_Plus : Original_LF__DOT__Basics_LF_Basics_modifier := Original_LF__DOT__Basics_LF_Basics_modifier.Plus
def Original_LF__DOT__Basics_LF_Basics_Natural : Original_LF__DOT__Basics_LF_Basics_modifier := Original_LF__DOT__Basics_LF_Basics_modifier.Natural
def Original_LF__DOT__Basics_LF_Basics_Minus : Original_LF__DOT__Basics_LF_Basics_modifier := Original_LF__DOT__Basics_LF_Basics_modifier.Minus

-- Grade type: Grade (l : letter) (m : modifier)
inductive Original_LF__DOT__Basics_LF_Basics_grade : Type where
  | Grade : Original_LF__DOT__Basics_LF_Basics_letter → Original_LF__DOT__Basics_LF_Basics_modifier → Original_LF__DOT__Basics_LF_Basics_grade

def Original_LF__DOT__Basics_LF_Basics_Grade : Original_LF__DOT__Basics_LF_Basics_letter → Original_LF__DOT__Basics_LF_Basics_modifier → Original_LF__DOT__Basics_LF_Basics_grade :=
  Original_LF__DOT__Basics_LF_Basics_grade.Grade

-- Comparison type: Eq, Lt, Gt
inductive Original_LF__DOT__Basics_LF_Basics_comparison : Type where
  | Eq : Original_LF__DOT__Basics_LF_Basics_comparison
  | Lt : Original_LF__DOT__Basics_LF_Basics_comparison
  | Gt : Original_LF__DOT__Basics_LF_Basics_comparison

def Original_LF__DOT__Basics_LF_Basics_Eq : Original_LF__DOT__Basics_LF_Basics_comparison := Original_LF__DOT__Basics_LF_Basics_comparison.Eq
def Original_LF__DOT__Basics_LF_Basics_Lt : Original_LF__DOT__Basics_LF_Basics_comparison := Original_LF__DOT__Basics_LF_Basics_comparison.Lt
def Original_LF__DOT__Basics_LF_Basics_Gt : Original_LF__DOT__Basics_LF_Basics_comparison := Original_LF__DOT__Basics_LF_Basics_comparison.Gt

-- grade_comparison is an axiom (Admitted in Coq)
axiom Original_LF__DOT__Basics_LF_Basics_grade__comparison :
  Original_LF__DOT__Basics_LF_Basics_grade → Original_LF__DOT__Basics_LF_Basics_grade → Original_LF__DOT__Basics_LF_Basics_comparison

-- lower_grade is an axiom (Admitted in Coq)
axiom Original_LF__DOT__Basics_LF_Basics_lower__grade :
  Original_LF__DOT__Basics_LF_Basics_grade → Original_LF__DOT__Basics_LF_Basics_grade

-- apply_late_policy
noncomputable def Original_LF__DOT__Basics_LF_Basics_apply__late__policy (late_days : nat) (g : Original_LF__DOT__Basics_LF_Basics_grade) : Original_LF__DOT__Basics_LF_Basics_grade :=
  match Original_LF__DOT__Basics_LF_Basics_ltb late_days (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))))))) with
  | Original_LF__DOT__Basics_LF_Basics_bool.true => g
  | Original_LF__DOT__Basics_LF_Basics_bool.false =>
    match Original_LF__DOT__Basics_LF_Basics_ltb late_days (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))))))))))))))) with
    | Original_LF__DOT__Basics_LF_Basics_bool.true => Original_LF__DOT__Basics_LF_Basics_lower__grade g
    | Original_LF__DOT__Basics_LF_Basics_bool.false =>
      match Original_LF__DOT__Basics_LF_Basics_ltb late_days (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))))))))))))))))))) with
      | Original_LF__DOT__Basics_LF_Basics_bool.true => Original_LF__DOT__Basics_LF_Basics_lower__grade (Original_LF__DOT__Basics_LF_Basics_lower__grade g)
      | Original_LF__DOT__Basics_LF_Basics_bool.false => Original_LF__DOT__Basics_LF_Basics_lower__grade (Original_LF__DOT__Basics_LF_Basics_lower__grade (Original_LF__DOT__Basics_LF_Basics_lower__grade g))

-- no_penalty_for_mostly_on_time is an axiom (Admitted theorem)
axiom Original_LF__DOT__Basics_LF_Basics_no__penalty__for__mostly__on__time :
  ∀ (late_days : nat) (g : Original_LF__DOT__Basics_LF_Basics_grade),
    Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_ltb late_days (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))))))) Original_LF__DOT__Basics_LF_Basics_true →
    Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_apply__late__policy late_days g) g

-- test_grade_comparison3 is an axiom (Admitted theorem)
axiom Original_LF__DOT__Basics_LF_Basics_test__grade__comparison3 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Basics_LF_Basics_grade__comparison
      (Original_LF__DOT__Basics_LF_Basics_Grade Original_LF__DOT__Basics_LF_Basics_F Original_LF__DOT__Basics_LF_Basics_Plus)
      (Original_LF__DOT__Basics_LF_Basics_Grade Original_LF__DOT__Basics_LF_Basics_F Original_LF__DOT__Basics_LF_Basics_Plus))
    Original_LF__DOT__Basics_LF_Basics_Eq

-- ============================================================
-- Original.LF_DOT_Poly definitions
-- ============================================================

-- Polymorphic list type
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

def Original_LF__DOT__Poly_LF_Poly_cons (X : Type) : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons

-- app function for list
def Original_LF__DOT__Poly_LF_Poly_app (X : Type) (l1 l2 : Original_LF__DOT__Poly_LF_Poly_list X) : Original_LF__DOT__Poly_LF_Poly_list X :=
  match l1 with
  | .nil => l2
  | .cons x xs => .cons x (Original_LF__DOT__Poly_LF_Poly_app X xs l2)

-- doit3times: applies f three times
def Original_LF__DOT__Poly_LF_Poly_doit3times (X : Type) (f : X → X) (n : X) : X :=
  f (f (f n))

-- test_plus3'' is Admitted
axiom Original_LF__DOT__Poly_LF_Poly_test__plus3'' :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Poly_LF_Poly_doit3times nat
      (fun x => Original_LF__DOT__Basics_LF_Basics_plus (nat.S (nat.S (nat.S nat.O))) x)
      _0)
    (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))))))

-- ============================================================
-- Original.LF_DOT_IndProp definitions
-- ============================================================

-- Regular expression type
inductive Original_LF__DOT__IndProp_LF_IndProp_reg__exp (T : Type) : Type where
  | EmptySet : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | EmptyStr : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Char : T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | App : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Union : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Star : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T

-- Constructors as definitions
def Original_LF__DOT__IndProp_LF_IndProp_EmptySet (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T := Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptySet
def Original_LF__DOT__IndProp_LF_IndProp_EmptyStr (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T := Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptyStr
def Original_LF__DOT__IndProp_LF_IndProp_Char (T : Type) : T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T := Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Char
def Original_LF__DOT__IndProp_LF_IndProp_App (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T := Original_LF__DOT__IndProp_LF_IndProp_reg__exp.App
def Original_LF__DOT__IndProp_LF_IndProp_Union (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T := Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Union
def Original_LF__DOT__IndProp_LF_IndProp_Star (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T := Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star

-- exp_match inductive type
inductive Original_LF__DOT__IndProp_LF_IndProp_exp__match {T : Type} :
    Original_LF__DOT__Poly_LF_Poly_list T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Prop where
  | MEmpty : Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_list.nil) (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptyStr)
  | MChar (x : T) : Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_list.cons x Original_LF__DOT__Poly_LF_Poly_list.nil) (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Char x)
  | MApp (s1 s2 : Original_LF__DOT__Poly_LF_Poly_list T) (re1 re2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
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

-- char_eps_suffix is Admitted
axiom Original_LF__DOT__IndProp_LF_IndProp_char__eps__suffix :
  ∀ (a : Ascii_ascii) (s : Original_LF__DOT__Poly_LF_Poly_list Ascii_ascii),
    iff (@Original_LF__DOT__IndProp_LF_IndProp_exp__match Ascii_ascii
           (Original_LF__DOT__Poly_LF_Poly_cons Ascii_ascii a s)
           (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Char a))
        (Corelib_Init_Logic_eq s (Original_LF__DOT__Poly_LF_Poly_nil Ascii_ascii))

-- n_lt_m__n_le_m is Admitted
axiom Original_LF__DOT__IndProp_LF_IndProp_n__lt__m____n__le__m : ∀ (n m : nat), lt n m → le n m

-- ============================================================
-- Original.LF_DOT_IndPrinciples definitions
-- ============================================================

-- Booltree type
inductive Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree : Type where
  | bt_empty : Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree
  | bt_leaf : Original_LF__DOT__Basics_LF_Basics_bool → Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree
  | bt_branch : Original_LF__DOT__Basics_LF_Basics_bool → Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree → Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree → Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree

-- The property type
def Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree__property__type : Type :=
  Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree → Prop

-- base_case is admitted in Original.v
axiom Original_LF__DOT__IndPrinciples_LF_IndPrinciples_base__case :
  (Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree → Prop) → Prop

-- leaf_case is admitted in Original.v
axiom Original_LF__DOT__IndPrinciples_LF_IndPrinciples_leaf__case :
  (Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree → Prop) → Prop

-- branch_case is admitted in Original.v
axiom Original_LF__DOT__IndPrinciples_LF_IndPrinciples_branch__case :
  (Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree → Prop) → Prop

-- booltree_ind_type is defined using the cases
def Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree__ind__type : Prop :=
  ∀ (P : Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree__property__type),
    Original_LF__DOT__IndPrinciples_LF_IndPrinciples_base__case P →
    Original_LF__DOT__IndPrinciples_LF_IndPrinciples_leaf__case P →
    Original_LF__DOT__IndPrinciples_LF_IndPrinciples_branch__case P →
    ∀ (b : Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree), P b

-- booltree_ind_type_correct is admitted in Original.v
axiom Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree__ind__type__correct :
  Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree__ind__type

-- ============================================================
-- Original.LF_DOT_Tactics definitions
-- ============================================================

-- sillyfun1 function
def Original_LF__DOT__Tactics_LF_Tactics_sillyfun1 (n : nat) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match Original_LF__DOT__Basics_LF_Basics_eqb n (nat.S (nat.S (nat.S nat.O))) with
  | Original_LF__DOT__Basics_LF_Basics_bool.true => Original_LF__DOT__Basics_LF_Basics_bool.false
  | Original_LF__DOT__Basics_LF_Basics_bool.false =>
    match Original_LF__DOT__Basics_LF_Basics_eqb n (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))) with
    | Original_LF__DOT__Basics_LF_Basics_bool.true => Original_LF__DOT__Basics_LF_Basics_bool.false
    | Original_LF__DOT__Basics_LF_Basics_bool.false => Original_LF__DOT__Basics_LF_Basics_bool.false

-- sillyfun1_odd is Admitted
axiom Original_LF__DOT__Tactics_LF_Tactics_sillyfun1__odd :
  ∀ (n : nat),
    Corelib_Init_Logic_eq (Original_LF__DOT__Tactics_LF_Tactics_sillyfun1 n) Original_LF__DOT__Basics_LF_Basics_true →
    Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_odd n) Original_LF__DOT__Basics_LF_Basics_true

-- ============================================================
-- Original.LF_DOT_Logic definitions
-- ============================================================

-- combine_odd_even is admitted in original
axiom Original_LF__DOT__Logic_LF_Logic_combine__odd__even : (nat → Prop) → (nat → Prop) → nat → Prop

-- combine_odd_even_elim_even is also admitted in original
axiom Original_LF__DOT__Logic_LF_Logic_combine__odd__even__elim__even :
  ∀ (Podd Peven : nat → Prop) (n : nat),
    Original_LF__DOT__Logic_LF_Logic_combine__odd__even Podd Peven n →
    Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_odd n) Original_LF__DOT__Basics_LF_Basics_false →
    Peven n

-- mul_eq_0_ternary is Admitted
axiom Original_LF__DOT__Logic_LF_Logic_mul__eq__0__ternary :
  ∀ (n m p : nat), iff (Corelib_Init_Logic_eq (Nat_mul (Nat_mul n m) p) _0)
                       (or (Corelib_Init_Logic_eq n _0)
                           (or (Corelib_Init_Logic_eq m _0)
                               (Corelib_Init_Logic_eq p _0)))

-- ============================================================
-- False type (empty type)
-- ============================================================
inductive myFalse : Prop where

-- ============================================================
-- Standard list type
-- ============================================================
inductive list (X : Type) : Type where
  | nil : list X
  | cons : X → list X → list X

def list_nil (X : Type) : list X := list.nil
def list_cons (X : Type) (h : X) (t : list X) : list X := list.cons h t

-- ============================================================
-- Additional definitions for main checkers
-- ============================================================

-- Multiplication for LF.Basics
def Original_LF__DOT__Basics_LF_Basics_mult : nat → nat → nat
  | nat.O, _ => nat.O
  | nat.S n, m => Original_LF__DOT__Basics_LF_Basics_plus m (Original_LF__DOT__Basics_LF_Basics_mult n m)

-- Build nat constants iteratively
def nat10 : nat := nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))))))
def nat100 : nat := Original_LF__DOT__Basics_LF_Basics_mult nat10 nat10
def nat1000 : nat := Original_LF__DOT__Basics_LF_Basics_mult nat10 nat100
def nat1001 : nat := nat.S nat1000

-- test_leb3' : (4 <=? 2) = false (Admitted in Original.v)
axiom Original_LF__DOT__Basics_LF_Basics_test__leb3' :
  Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_leb (S (S (S (S nat.O)))) (S (S nat.O))) Original_LF__DOT__Basics_LF_Basics_false

-- even_S : forall n : nat, even (S n) = negb (even n) (Admitted in Original.v)
axiom Original_LF__DOT__Induction_LF_Induction_even__S :
  ∀ (n : nat), Corelib_Init_Logic_eq 
    (Original_LF__DOT__Basics_LF_Basics_even (S n)) 
    (Original_LF__DOT__Basics_LF_Basics_negb (Original_LF__DOT__Basics_LF_Basics_even n))

-- factor_is_O : forall n m : nat, n = 0 \/ m = 0 -> n * m = 0 (Admitted in Original.v)
axiom Original_LF__DOT__Logic_LF_Logic_factor__is__O :
  ∀ (n m : nat), or (Corelib_Init_Logic_eq n nat.O) (Corelib_Init_Logic_eq m nat.O) → 
    Corelib_Init_Logic_eq (Nat_mul n m) nat.O

-- or_intro_l : forall A B : Prop, A -> A \/ B (Admitted in Original.v)
axiom Original_LF__DOT__Logic_LF_Logic_or__intro__l :
  ∀ (A B : Prop), A → or A B

-- or_commut : forall P Q : Prop, P \/ Q -> Q \/ P (Admitted in Original.v)
axiom Original_LF__DOT__Logic_LF_Logic_or__commut :
  ∀ (P Q : Prop), or P Q → or Q P

-- even_1000' : even 1000 = true (Admitted in Original.v)
axiom Original_LF__DOT__Logic_LF_Logic_even__1000' :
  Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_even nat1000) Original_LF__DOT__Basics_LF_Basics_true

-- not_even_1001 : even 1001 = false (Admitted in Original.v)
axiom Original_LF__DOT__Logic_LF_Logic_not__even__1001 :
  Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_even nat1001) Original_LF__DOT__Basics_LF_Basics_false

-- leb_correct : forall n m, n <= m -> n <=? m = true (Admitted in Original.v)
axiom Original_LF__DOT__IndProp_LF_IndProp_leb__correct :
  ∀ (n m : nat), le n m → Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_leb n m) Original_LF__DOT__Basics_LF_Basics_true

-- booltree_ind_type_correct, base_case, leaf_case, branch_case are already defined above
