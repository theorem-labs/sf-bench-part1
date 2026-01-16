-- Comprehensive Lean translation merging all needed definitions
-- NOTE: After export, the following sed operations must be applied to Imported.out:
--   sed -i "s/Original_LF__DOT__Imp_LF_Imp_AExp_fooSQUOTE/Original_LF__DOT__Imp_LF_Imp_AExp_foo'/g" /workdir/Imported.out
--   sed -i "s/Original_LF__DOT__IndPrinciples_LF_IndPrinciples_P__m0rSQUOTE/Original_LF__DOT__IndPrinciples_LF_IndPrinciples_P__m0r'/g" /workdir/Imported.out
set_option linter.all false
set_option autoImplicit false

-- ============================================================================
-- Core types: True, False, Equality
-- ============================================================================

-- True in Prop (will become SProp in Rocq)
inductive TrueType : Prop where
  | I : TrueType

def TrueType_I := TrueType.I

-- False in Prop (will become SProp in Rocq)  
inductive FalseType : Prop where

-- Equality in Prop for Type arguments
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl a

-- Equality in Prop for Prop arguments
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

def Corelib_Init_Logic_eq_Prop_refl {A : Prop} (a : A) : Corelib_Init_Logic_eq_Prop a a :=
  Corelib_Init_Logic_eq_Prop.refl a

-- Logic.not
def Logic_not (P : Prop) : Prop := P → FalseType

-- ============================================================================
-- Boolean type (custom to avoid Lean's Bool conflicts)
-- ============================================================================

inductive mybool : Type where
  | mytrue : mybool
  | myfalse : mybool

def mybool_mytrue : mybool := mybool.mytrue
def mybool_myfalse : mybool := mybool.myfalse
def my_true : mybool := mybool.mytrue
def my_false : mybool := mybool.myfalse
def _bool : Type := mybool

-- ============================================================================
-- Natural numbers (custom nat)
-- ============================================================================

inductive nat : Type where
  | O : nat
  | S : nat → nat

def nat_O := nat.O
def nat_S := nat.S
def S := nat.S
def O := nat.O
def zero_nat := nat.O

def nat_add : nat → nat → nat
  | nat.O, m => m
  | nat.S n, m => nat.S (nat_add n m)

def nat_sub : nat → nat → nat
  | n, nat.O => n
  | nat.O, nat.S _ => nat.O
  | nat.S n, nat.S m => nat_sub n m

def nat_mul : nat → nat → nat
  | nat.O, _ => nat.O
  | nat.S n, m => nat_add m (nat_mul n m)

def nat_pred : nat → nat
  | nat.O => nat.O
  | nat.S n => n

def Nat_add := nat_add
def Nat_sub := nat_sub
def Nat_mul := nat_mul
def Nat_pred := nat_pred

def nat_eqb : nat → nat → mybool
  | nat.O, nat.O => mybool.mytrue
  | nat.S n, nat.S m => nat_eqb n m
  | _, _ => mybool.myfalse

def nat_leb : nat → nat → mybool
  | nat.O, _ => mybool.mytrue
  | nat.S _, nat.O => mybool.myfalse
  | nat.S n, nat.S m => nat_leb n m

def bool_negb : mybool → mybool
  | mybool.mytrue => mybool.myfalse
  | mybool.myfalse => mybool.mytrue

def bool_andb : mybool → mybool → mybool
  | mybool.mytrue, b => b
  | mybool.myfalse, _ => mybool.myfalse

def bool_eqb : mybool → mybool → mybool
  | mybool.mytrue, mybool.mytrue => mybool.mytrue
  | mybool.myfalse, mybool.myfalse => mybool.mytrue
  | _, _ => mybool.myfalse

-- ============================================================================
-- Option type (custom)
-- ============================================================================

inductive option (A : Type) : Type where
  | None : option A
  | Some : A → option A

def None {A : Type} : option A := option.None
def Some {A : Type} (a : A) : option A := option.Some a

-- ============================================================================
-- Product type
-- ============================================================================

inductive prod (A B : Type) : Type where
  | pair : A → B → prod A B

def pair {A B : Type} (a : A) (b : B) : prod A B := prod.pair a b

-- ============================================================================
-- List type
-- ============================================================================

inductive list (A : Type) : Type where
  | nil : list A
  | cons : A → list A → list A

def nil {A : Type} : list A := list.nil
def cons {A : Type} (a : A) (l : list A) : list A := list.cons a l

-- ============================================================================
-- Or type (as a structure with an eliminator field for SProp-compatible elimination)
-- ============================================================================

structure or (A B : Prop) : Prop where
  intro ::
  elim : ∀ C : Prop, (A → C) → (B → C) → C

-- Smart constructors for or
def or_inl {A B : Prop} (a : A) : or A B := ⟨fun _ f _ => f a⟩
def or_inr {A B : Prop} (b : B) : or A B := ⟨fun _ _ g => g b⟩

-- ============================================================================
-- And type (conjunction)
-- ============================================================================

structure and (A B : Prop) : Prop where
  intro ::
  left : A
  right : B

def and_intro {A B : Prop} (a : A) (b : B) : and A B := ⟨a, b⟩

-- ============================================================================
-- Ascii type (8 booleans) - using our custom mybool
-- ============================================================================

inductive Ascii_ascii : Type where
  | Ascii : mybool → mybool → mybool → mybool → mybool → mybool → mybool → mybool → Ascii_ascii

def Ascii := Ascii_ascii
def Ascii_Ascii := Ascii_ascii.Ascii

def Ascii_eqb (a1 a2 : Ascii_ascii) : mybool :=
  match a1, a2 with
  | Ascii_ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7, Ascii_ascii.Ascii c0 c1 c2 c3 c4 c5 c6 c7 =>
    bool_andb (bool_eqb b0 c0) (bool_andb (bool_eqb b1 c1) (bool_andb (bool_eqb b2 c2) (bool_andb (bool_eqb b3 c3)
    (bool_andb (bool_eqb b4 c4) (bool_andb (bool_eqb b5 c5) (bool_andb (bool_eqb b6 c6) (bool_eqb b7 c7)))))))

-- ============================================================================
-- String type
-- ============================================================================

inductive String_string : Type where
  | EmptyString : String_string
  | String : Ascii_ascii → String_string → String_string

def String_EmptyString := String_string.EmptyString
def String_String := String_string.String

def String_eqb : String_string → String_string → mybool
  | String_string.EmptyString, String_string.EmptyString => mybool.mytrue
  | String_string.String c1 s1, String_string.String c2 s2 => bool_andb (Ascii_eqb c1 c2) (String_eqb s1 s2)
  | _, _ => mybool.myfalse

-- Character constants for Imp
def char_X : Ascii_ascii := Ascii_ascii.Ascii mybool.myfalse mybool.myfalse mybool.myfalse mybool.mytrue mybool.mytrue mybool.mytrue mybool.mytrue mybool.myfalse
def char_Y : Ascii_ascii := Ascii_ascii.Ascii mybool.mytrue mybool.myfalse mybool.myfalse mybool.mytrue mybool.mytrue mybool.mytrue mybool.mytrue mybool.myfalse
def char_Z : Ascii_ascii := Ascii_ascii.Ascii mybool.myfalse mybool.mytrue mybool.myfalse mybool.mytrue mybool.mytrue mybool.mytrue mybool.mytrue mybool.myfalse

-- ============================================================================
-- LF.Basics types: letter, modifier, grade
-- ============================================================================

-- Letter type: A, B, C, D, F
inductive Original_LF__DOT__Basics_LF_Basics_letter : Type where
  | A : Original_LF__DOT__Basics_LF_Basics_letter
  | B : Original_LF__DOT__Basics_LF_Basics_letter
  | C : Original_LF__DOT__Basics_LF_Basics_letter
  | D : Original_LF__DOT__Basics_LF_Basics_letter
  | F : Original_LF__DOT__Basics_LF_Basics_letter

def Original_LF__DOT__Basics_LF_Basics_A : Original_LF__DOT__Basics_LF_Basics_letter :=
  Original_LF__DOT__Basics_LF_Basics_letter.A

-- Modifier type: Plus, Natural, Minus
inductive Original_LF__DOT__Basics_LF_Basics_modifier : Type where
  | Plus : Original_LF__DOT__Basics_LF_Basics_modifier
  | Natural : Original_LF__DOT__Basics_LF_Basics_modifier
  | Minus : Original_LF__DOT__Basics_LF_Basics_modifier

def Original_LF__DOT__Basics_LF_Basics_Natural : Original_LF__DOT__Basics_LF_Basics_modifier :=
  Original_LF__DOT__Basics_LF_Basics_modifier.Natural

def Original_LF__DOT__Basics_LF_Basics_Minus : Original_LF__DOT__Basics_LF_Basics_modifier :=
  Original_LF__DOT__Basics_LF_Basics_modifier.Minus

-- Grade type: Grade (l : letter) (m : modifier)
inductive Original_LF__DOT__Basics_LF_Basics_grade : Type where
  | Grade : Original_LF__DOT__Basics_LF_Basics_letter → Original_LF__DOT__Basics_LF_Basics_modifier → Original_LF__DOT__Basics_LF_Basics_grade

def Original_LF__DOT__Basics_LF_Basics_Grade : Original_LF__DOT__Basics_LF_Basics_letter → Original_LF__DOT__Basics_LF_Basics_modifier → Original_LF__DOT__Basics_LF_Basics_grade :=
  Original_LF__DOT__Basics_LF_Basics_grade.Grade

-- bool type for LF.Basics (use mybool)
def Original_LF__DOT__Basics_LF_Basics_bool : Type := mybool
def Original_LF__DOT__Basics_LF_Basics_true : mybool := mybool.mytrue
def Original_LF__DOT__Basics_LF_Basics_false : mybool := mybool.myfalse

-- lower_grade is an axiom (Admitted) in the original
axiom Original_LF__DOT__Basics_LF_Basics_lower__grade : Original_LF__DOT__Basics_LF_Basics_grade → Original_LF__DOT__Basics_LF_Basics_grade

-- lower_grade_A_Natural is an axiom stating lower_grade (Grade A Natural) = (Grade A Minus)
axiom Original_LF__DOT__Basics_LF_Basics_lower__grade__A__Natural :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Basics_LF_Basics_lower__grade
      (Original_LF__DOT__Basics_LF_Basics_Grade Original_LF__DOT__Basics_LF_Basics_A Original_LF__DOT__Basics_LF_Basics_Natural))
    (Original_LF__DOT__Basics_LF_Basics_Grade Original_LF__DOT__Basics_LF_Basics_A Original_LF__DOT__Basics_LF_Basics_Minus)

-- ============================================================================
-- LF.Lists types: natlist, natoption, etc.
-- ============================================================================

-- natlist type (custom list of nats)
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natlist : Type where
  | nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist

def Original_LF__DOT__Lists_LF_Lists_NatList_nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil

def Original_LF__DOT__Lists_LF_Lists_NatList_cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons

-- bag is a type alias for natlist
def Original_LF__DOT__Lists_LF_Lists_NatList_bag : Type := Original_LF__DOT__Lists_LF_Lists_NatList_natlist

-- app function (list append)
def Original_LF__DOT__Lists_LF_Lists_NatList_app : Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil, l2 => l2
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h t, l2 => 
      Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h (Original_LF__DOT__Lists_LF_Lists_NatList_app t l2)

-- natoption type
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natoption : Type where
  | None : Original_LF__DOT__Lists_LF_Lists_NatList_natoption
  | Some : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natoption

def Original_LF__DOT__Lists_LF_Lists_NatList_None : Original_LF__DOT__Lists_LF_Lists_NatList_natoption :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natoption.None

def Original_LF__DOT__Lists_LF_Lists_NatList_Some : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natoption :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natoption.Some

-- hd_error function (axiom since Admitted in original)
axiom Original_LF__DOT__Lists_LF_Lists_NatList_hd__error : Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natoption

-- test_hd_error1 axiom
axiom Original_LF__DOT__Lists_LF_Lists_NatList_test__hd__error1 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_hd__error Original_LF__DOT__Lists_LF_Lists_NatList_nil)
    Original_LF__DOT__Lists_LF_Lists_NatList_None

-- add function for bags (axiom since Admitted in original)
axiom Original_LF__DOT__Lists_LF_Lists_NatList_add : nat → Original_LF__DOT__Lists_LF_Lists_NatList_bag → Original_LF__DOT__Lists_LF_Lists_NatList_bag

-- test_add1 axiom
axiom Original_LF__DOT__Lists_LF_Lists_NatList_test__add1 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_add (nat.S nat.O) 
      (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S (nat.S (nat.S (nat.S nat.O))))
        (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S nat.O)
          Original_LF__DOT__Lists_LF_Lists_NatList_nil)))
    (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S nat.O)
      (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S (nat.S (nat.S (nat.S nat.O))))
        (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S nat.O)
          Original_LF__DOT__Lists_LF_Lists_NatList_nil)))

-- count function (axiom since Admitted in original)
axiom Original_LF__DOT__Lists_LF_Lists_NatList_count : nat → Original_LF__DOT__Lists_LF_Lists_NatList_bag → nat

-- app_assoc4 axiom (Admitted)
axiom Original_LF__DOT__Lists_LF_Lists_NatList_app__assoc4 :
  ∀ (l1 l2 l3 l4 : Original_LF__DOT__Lists_LF_Lists_NatList_natlist),
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_app l1 
      (Original_LF__DOT__Lists_LF_Lists_NatList_app l2 
        (Original_LF__DOT__Lists_LF_Lists_NatList_app l3 l4)))
    (Original_LF__DOT__Lists_LF_Lists_NatList_app 
      (Original_LF__DOT__Lists_LF_Lists_NatList_app 
        (Original_LF__DOT__Lists_LF_Lists_NatList_app l1 l2) l3) l4)

-- ============================================================================
-- LF.Maps types: total_map, partial_map, t_update, update, includedin
-- ============================================================================

-- total_map is a function type: string -> A
def Original_LF__DOT__Maps_LF_Maps_total__map (A : Type) : Type := String_string → A

-- partial_map is total_map (option A)
def Original_LF__DOT__Maps_LF_Maps_partial__map (A : Type) : Type := 
  Original_LF__DOT__Maps_LF_Maps_total__map (option A)

-- Bool case analysis for t_update
def mybool_case (A : Type) (b : mybool) (vtrue vfalse : A) : A :=
  match b with
  | mybool.mytrue => vtrue
  | mybool.myfalse => vfalse

-- t_empty
def Original_LF__DOT__Maps_LF_Maps_t__empty (A : Type) (v : A) : Original_LF__DOT__Maps_LF_Maps_total__map A :=
  fun _ => v

-- t_update: total map update
def Original_LF__DOT__Maps_LF_Maps_t__update (A : Type) (m : Original_LF__DOT__Maps_LF_Maps_total__map A) 
    (x : String_string) (v : A) : Original_LF__DOT__Maps_LF_Maps_total__map A :=
  fun x' => mybool_case A (String_eqb x x') v (m x')

-- update: partial map update (uses t_update with Some v)
def Original_LF__DOT__Maps_LF_Maps_update (A : Type) (m : Original_LF__DOT__Maps_LF_Maps_partial__map A) 
    (x : String_string) (v : A) : Original_LF__DOT__Maps_LF_Maps_partial__map A :=
  Original_LF__DOT__Maps_LF_Maps_t__update (option A) m x (option.Some v)

-- includedin: forall x v, m x = Some v -> m' x = Some v
def Original_LF__DOT__Maps_LF_Maps_includedin {A : Type} 
  (m m' : Original_LF__DOT__Maps_LF_Maps_partial__map A) : Prop :=
  ∀ (x : String_string) (v : A), Corelib_Init_Logic_eq (m x) (Some v) → Corelib_Init_Logic_eq (m' x) (Some v)

-- includedin_update: Admitted lemma - translate as axiom
axiom Original_LF__DOT__Maps_LF_Maps_includedin__update :
  ∀ (A : Type) (m m' : Original_LF__DOT__Maps_LF_Maps_partial__map A) (x : String_string) (vx : A),
  Original_LF__DOT__Maps_LF_Maps_includedin m m' →
  Original_LF__DOT__Maps_LF_Maps_includedin (Original_LF__DOT__Maps_LF_Maps_update A m x vx) (Original_LF__DOT__Maps_LF_Maps_update A m' x vx)

-- update_neq: Admitted lemma - translate as axiom
axiom Original_LF__DOT__Maps_LF_Maps_update__neq : 
  ∀ (A : Type) (m : Original_LF__DOT__Maps_LF_Maps_partial__map A) 
    (x1 x2 : String_string) (v : A),
    Logic_not (Corelib_Init_Logic_eq x2 x1) →
    Corelib_Init_Logic_eq (Original_LF__DOT__Maps_LF_Maps_update A m x2 v x1) (m x1)

-- ============================================================================
-- LF.IndProp types: reg_exp, derive, match_eps
-- ============================================================================

-- Regular expression type
inductive Original_LF__DOT__IndProp_LF_IndProp_reg__exp (T : Type) : Type where
  | EmptySet : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | EmptyStr : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Char : T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | App : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Union : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Star : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T

-- Aliases for reg_exp constructors
def Original_LF__DOT__IndProp_LF_IndProp_EmptySet (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptySet

def Original_LF__DOT__IndProp_LF_IndProp_EmptyStr (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptyStr

def Original_LF__DOT__IndProp_LF_IndProp_Char {T : Type} : T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Char

def Original_LF__DOT__IndProp_LF_IndProp_App {T : Type} : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.App

def Original_LF__DOT__IndProp_LF_IndProp_Union {T : Type} : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Union

def Original_LF__DOT__IndProp_LF_IndProp_Star {T : Type} : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star

-- Character constant c for tests (ASCII 'c' = 01100011)
def Original_LF__DOT__IndProp_LF_IndProp_c : Ascii_ascii :=
  Ascii_ascii.Ascii mybool.mytrue mybool.mytrue mybool.myfalse mybool.myfalse mybool.myfalse mybool.mytrue mybool.mytrue mybool.myfalse

-- derive function (axiom since Admitted in Original.v)
axiom Original_LF__DOT__IndProp_LF_IndProp_derive : 
  Ascii_ascii → Original_LF__DOT__IndProp_LF_IndProp_reg__exp Ascii_ascii → Original_LF__DOT__IndProp_LF_IndProp_reg__exp Ascii_ascii

-- match_eps function (axiom since Admitted in Original.v)
axiom Original_LF__DOT__IndProp_LF_IndProp_match__eps : 
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp Ascii_ascii → mybool

-- test_der4 theorem (axiom since Admitted in Original.v)
axiom Original_LF__DOT__IndProp_LF_IndProp_test__der4 : 
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__IndProp_LF_IndProp_match__eps 
      (Original_LF__DOT__IndProp_LF_IndProp_derive Original_LF__DOT__IndProp_LF_IndProp_c 
        (Original_LF__DOT__IndProp_LF_IndProp_App 
          (Original_LF__DOT__IndProp_LF_IndProp_EmptyStr Ascii_ascii) 
          (Original_LF__DOT__IndProp_LF_IndProp_Char Original_LF__DOT__IndProp_LF_IndProp_c)))) 
    mybool.mytrue

-- ============================================================================
-- LF.Imp types: aexp with division (aevalR_division)
-- ============================================================================

-- aexp type with division
inductive Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp : Type where
  | ANum : nat → Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp
  | APlus : Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp → Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp → Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp
  | AMinus : Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp → Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp → Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp
  | AMult : Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp → Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp → Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp
  | ADiv : Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp → Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp → Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp

-- gt relation (needed for division)
inductive gt : nat → nat → Prop where
  | gt_succ : ∀ (n : nat), gt (nat.S n) nat.O
  | gt_step : ∀ (m n : nat), gt m n → gt (nat.S m) (nat.S n)

-- aevalR evaluation relation with division
inductive Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR : Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp → nat → Prop where
  | E_ANum : ∀ (n : nat),
      Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR (Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp.ANum n) n
  | E_APlus : ∀ (a1 a2 : Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp) (n1 n2 : nat),
      Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR a1 n1 →
      Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR a2 n2 →
      Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR (Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp.APlus a1 a2) (nat_add n1 n2)
  | E_AMinus : ∀ (a1 a2 : Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp) (n1 n2 : nat),
      Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR a1 n1 →
      Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR a2 n2 →
      Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR (Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp.AMinus a1 a2) (nat_sub n1 n2)
  | E_AMult : ∀ (a1 a2 : Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp) (n1 n2 : nat),
      Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR a1 n1 →
      Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR a2 n2 →
      Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR (Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp.AMult a1 a2) (nat_mul n1 n2)
  | E_ADiv : ∀ (a1 a2 : Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp) (n1 n2 n3 : nat),
      Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR a1 n1 →
      Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR a2 n2 →
      gt n2 nat.O →
      nat_mul n2 n3 = n1 →
      Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR (Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp.ADiv a1 a2) n3

-- ============================================================================
-- LF.AltAuto: intuition_succeed1
-- ============================================================================

-- intuition_succeed1: forall P : Prop, P -> P (identity function on propositions)
-- This is Admitted in the original but we can define it
def Original_LF__DOT__AltAuto_LF_AltAuto_intuition__succeed1 : ∀ (P : Prop), P → P := 
  fun P p => p

-- ============================================================================
-- List_In (used in some places)
-- ============================================================================

def List_In {A : Type} (a : A) : list A → Prop
  | list.nil => FalseType
  | list.cons x xs => or (Corelib_Init_Logic_eq a x) (List_In a xs)

-- ============================================================================
-- ex (exists)
-- ============================================================================

inductive ex {A : Type} (P : A → Prop) : Prop where
  | intro : ∀ (x : A), P x → ex P

def ex_intro {A : Type} {P : A → Prop} (x : A) (h : P x) : ex P := ex.intro x h

-- ============================================================================
-- iff (if and only if)
-- ============================================================================

structure iff (A B : Prop) : Prop where
  intro :: 
  mp : A → B
  mpr : B → A

def iff_intro {A B : Prop} (h1 : A → B) (h2 : B → A) : iff A B := iff.intro h1 h2

-- ============================================================================
-- le (less than or equal) as inductive proposition
-- ============================================================================

inductive le : nat → nat → Prop where
  | le_n (n : nat) : le n n
  | le_S (n m : nat) : le n m → le n (nat.S m)

-- le_Sn_le theorem (Admitted in original)
axiom Original_LF_Rel_le__Sn__le : ∀ (n m : nat), le (nat.S n) m → le n m

-- ============================================================================
-- LF.Basics: minustwo function
-- ============================================================================

def Original_LF__DOT__Basics_LF_Basics_minustwo : nat → nat
  | nat.O => nat.O
  | nat.S nat.O => nat.O
  | nat.S (nat.S n') => n'

-- ============================================================================
-- LF.Imp types: aexp, bexp, state (for Imp with identifiers)
-- ============================================================================

-- aexp with identifiers (for the main Imp language)
inductive Original_LF__DOT__Imp_LF_Imp_aexp : Type where
  | ANum : nat → Original_LF__DOT__Imp_LF_Imp_aexp
  | AId : String_string → Original_LF__DOT__Imp_LF_Imp_aexp
  | APlus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp
  | AMinus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp
  | AMult : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp

-- bexp
inductive Original_LF__DOT__Imp_LF_Imp_bexp : Type where
  | BTrue : Original_LF__DOT__Imp_LF_Imp_bexp
  | BFalse : Original_LF__DOT__Imp_LF_Imp_bexp
  | BEq : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BNeq : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BLe : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BGt : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BNot : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BAnd : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp

-- state is total_map nat
def Original_LF__DOT__Imp_LF_Imp_state : Type := Original_LF__DOT__Maps_LF_Maps_total__map nat

-- ============================================================================
-- LF.Imp.BreakImp types: result, com with CBreak, ceval
-- ============================================================================

-- result type
inductive Original_LF__DOT__Imp_LF_Imp_BreakImp_result : Type where
  | SContinue : Original_LF__DOT__Imp_LF_Imp_BreakImp_result
  | SBreak : Original_LF__DOT__Imp_LF_Imp_BreakImp_result

def Original_LF__DOT__Imp_LF_Imp_BreakImp_SContinue := Original_LF__DOT__Imp_LF_Imp_BreakImp_result.SContinue
def Original_LF__DOT__Imp_LF_Imp_BreakImp_SBreak := Original_LF__DOT__Imp_LF_Imp_BreakImp_result.SBreak

-- com type with CBreak
inductive Original_LF__DOT__Imp_LF_Imp_BreakImp_com : Type where
  | CSkip : Original_LF__DOT__Imp_LF_Imp_BreakImp_com
  | CBreak : Original_LF__DOT__Imp_LF_Imp_BreakImp_com
  | CAsgn : String_string → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_BreakImp_com
  | CSeq : Original_LF__DOT__Imp_LF_Imp_BreakImp_com → Original_LF__DOT__Imp_LF_Imp_BreakImp_com → Original_LF__DOT__Imp_LF_Imp_BreakImp_com
  | CIf : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_BreakImp_com → Original_LF__DOT__Imp_LF_Imp_BreakImp_com → Original_LF__DOT__Imp_LF_Imp_BreakImp_com
  | CWhile : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_BreakImp_com → Original_LF__DOT__Imp_LF_Imp_BreakImp_com

def Original_LF__DOT__Imp_LF_Imp_BreakImp_CBreak := Original_LF__DOT__Imp_LF_Imp_BreakImp_com.CBreak
def Original_LF__DOT__Imp_LF_Imp_BreakImp_CSeq := Original_LF__DOT__Imp_LF_Imp_BreakImp_com.CSeq

-- ceval is an inductive relation for BreakImp
-- NOTE: In the original Rocq, this has only one constructor E_Skip
-- Use inline type to match expected signature in Interface
inductive Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval : 
  Original_LF__DOT__Imp_LF_Imp_BreakImp_com → 
  (String_string → nat) → 
  Original_LF__DOT__Imp_LF_Imp_BreakImp_result → 
  (String_string → nat) → 
  Prop where
  | E_Skip : ∀ (st : String_string → nat),
      Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval 
        Original_LF__DOT__Imp_LF_Imp_BreakImp_com.CSkip 
        st 
        Original_LF__DOT__Imp_LF_Imp_BreakImp_result.SContinue 
        st

-- break_ignore theorem (Admitted)
axiom Original_LF__DOT__Imp_LF_Imp_BreakImp_break__ignore :
  ∀ (c : Original_LF__DOT__Imp_LF_Imp_BreakImp_com) 
    (st st' : String_string → nat)
    (s : Original_LF__DOT__Imp_LF_Imp_BreakImp_result),
    Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval 
      (Original_LF__DOT__Imp_LF_Imp_BreakImp_CSeq Original_LF__DOT__Imp_LF_Imp_BreakImp_CBreak c) 
      st s st' →
    Corelib_Init_Logic_eq st st'

-- ceval_deterministic theorem (Admitted)
axiom Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval__deterministic :
  ∀ (c : Original_LF__DOT__Imp_LF_Imp_BreakImp_com)
    (st st1 st2 : String_string → nat)
    (s1 s2 : Original_LF__DOT__Imp_LF_Imp_BreakImp_result),
    Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval c st s1 st1 →
    Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval c st s2 st2 →
    and (Corelib_Init_Logic_eq st1 st2) (Corelib_Init_Logic_eq s1 s2)

-- ============================================================================
-- LF.Imp.AExp: foo and foo' theorems (Admitted)
-- ============================================================================

-- foo' is admitted directly as an axiom (same statement as foo)
axiom Original_LF__DOT__Imp_LF_Imp_AExp_fooSQUOTE :
  ∀ (n : nat), Corelib_Init_Logic_eq (nat_leb nat.O n) mybool.mytrue

-- ============================================================================
-- LF.IndPrinciples: P_m0r' definition
-- ============================================================================

def Original_LF__DOT__IndPrinciples_LF_IndPrinciples_P__m0rSQUOTE : nat → Prop :=
  fun n => Corelib_Init_Logic_eq (nat_mul n nat.O) nat.O

-- ============================================================================
-- LF.Lists: rev function for natlist
-- ============================================================================

def Original_LF__DOT__Lists_LF_Lists_NatList_rev : Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil => Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h t => 
      Original_LF__DOT__Lists_LF_Lists_NatList_app 
        (Original_LF__DOT__Lists_LF_Lists_NatList_rev t) 
        (Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil)

-- rev_involutive theorem (Admitted)
axiom Original_LF__DOT__Lists_LF_Lists_NatList_rev__involutive :
  ∀ (l : Original_LF__DOT__Lists_LF_Lists_NatList_natlist),
    Corelib_Init_Logic_eq (Original_LF__DOT__Lists_LF_Lists_NatList_rev (Original_LF__DOT__Lists_LF_Lists_NatList_rev l)) l

-- ============================================================================
-- LF.Logic: mult_is_O theorem (Admitted)
-- ============================================================================

axiom Original_LF__DOT__Logic_LF_Logic_mult__is__O :
  ∀ (n m : nat), Corelib_Init_Logic_eq (nat_mul n m) nat.O → or (Corelib_Init_Logic_eq n nat.O) (Corelib_Init_Logic_eq m nat.O)

-- ============================================================================
-- LF.Tactics: trans_eq_exercise theorem (Admitted)
-- ============================================================================

axiom Original_LF__DOT__Tactics_LF_Tactics_trans__eq__exercise :
  ∀ (n m o p : nat),
    Corelib_Init_Logic_eq m (nat_add (nat_add o p) nat.O) →
    Corelib_Init_Logic_eq n (nat_add m nat.O) →
    Corelib_Init_Logic_eq n (nat_add o p)

-- ============================================================================
-- LF.ProofObjects.Props: True type and p_implies_true theorem
-- ============================================================================

inductive Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_True : Prop where
  | I : Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_True

def Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_p__implies__true :
  ∀ (P : Prop), P → Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_True :=
  fun _ _ => Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_True.I

-- ============================================================================
-- LF.AltAuto: contras' theorem (Admitted)
-- ============================================================================

axiom Original_LF__DOT__AltAuto_LF_AltAuto_contras' :
  ∀ (P : Prop), P → Logic_not P → Corelib_Init_Logic_eq nat.O (nat.S nat.O)

-- ============================================================================
-- LF.IndProp: test_der5 theorem (Admitted)
-- ============================================================================

axiom Original_LF__DOT__IndProp_LF_IndProp_test__der5 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__IndProp_LF_IndProp_match__eps
      (Original_LF__DOT__IndProp_LF_IndProp_derive Original_LF__DOT__IndProp_LF_IndProp_c
        (Original_LF__DOT__IndProp_LF_IndProp_Star (Original_LF__DOT__IndProp_LF_IndProp_Char Original_LF__DOT__IndProp_LF_IndProp_c))))
    mybool.mytrue

