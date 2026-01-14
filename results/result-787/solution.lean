-- Translation of Rocq definitions for apply_late_policy_unfold and its dependencies

-- We need a custom True type - we'll manually rename MyTrue to True in the .out file
inductive MyTrue : Prop where
  | intro : MyTrue

-- Equality in Prop (will become SProp in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl a

-- Equality for Prop arguments (will become SProp equality in Rocq)
inductive Corelib_Init_Logic_eq_Prop (A : Prop) (a : A) : A → Prop where
  | refl : Corelib_Init_Logic_eq_Prop A a a

def Corelib_Init_Logic_eq_Prop_refl (A : Prop) (a : A) : Corelib_Init_Logic_eq_Prop A a a :=
  Corelib_Init_Logic_eq_Prop.refl

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Boolean type (matching LF.Basics.bool)
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- The recursor for bool (matching Rocq's bool_rec)
def Original_LF__DOT__Basics_LF_Basics_bool__rec {motive : Original_LF__DOT__Basics_LF_Basics_bool → Sort u}
  (htrue : motive Original_LF__DOT__Basics_LF_Basics_true)
  (hfalse : motive Original_LF__DOT__Basics_LF_Basics_false)
  (b : Original_LF__DOT__Basics_LF_Basics_bool) : motive b :=
  match b with
  | .true => htrue
  | .false => hfalse

-- Letter type: A, B, C, D, F
inductive Original_LF__DOT__Basics_LF_Basics_letter : Type where
  | A : Original_LF__DOT__Basics_LF_Basics_letter
  | B : Original_LF__DOT__Basics_LF_Basics_letter
  | C : Original_LF__DOT__Basics_LF_Basics_letter
  | D : Original_LF__DOT__Basics_LF_Basics_letter
  | F : Original_LF__DOT__Basics_LF_Basics_letter

-- Modifier type: Plus, Natural, Minus
inductive Original_LF__DOT__Basics_LF_Basics_modifier : Type where
  | Plus : Original_LF__DOT__Basics_LF_Basics_modifier
  | Natural : Original_LF__DOT__Basics_LF_Basics_modifier
  | Minus : Original_LF__DOT__Basics_LF_Basics_modifier

-- Grade type: Grade (l : letter) (m : modifier)
inductive Original_LF__DOT__Basics_LF_Basics_grade : Type where
  | Grade : Original_LF__DOT__Basics_LF_Basics_letter → Original_LF__DOT__Basics_LF_Basics_modifier → Original_LF__DOT__Basics_LF_Basics_grade

-- ltb is an axiom (Admitted) in the original
axiom Original_LF__DOT__Basics_LF_Basics_ltb : nat → nat → Original_LF__DOT__Basics_LF_Basics_bool

-- lower_grade is an axiom (Admitted) in the original
axiom Original_LF__DOT__Basics_LF_Basics_lower__grade : Original_LF__DOT__Basics_LF_Basics_grade → Original_LF__DOT__Basics_LF_Basics_grade

-- apply_late_policy defined in terms of ltb and lower_grade
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

-- apply_late_policy_unfold is an axiom (Admitted theorem) in the original
-- It states that apply_late_policy unfolds to a specific form using bool_rec
axiom Original_LF__DOT__Basics_LF_Basics_apply__late__policy__unfold :
  ∀ (late_days : nat) (g : Original_LF__DOT__Basics_LF_Basics_grade),
    Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_apply__late__policy late_days g)
      (Original_LF__DOT__Basics_LF_Basics_bool__rec (motive := fun _ => Original_LF__DOT__Basics_LF_Basics_grade) g
        (Original_LF__DOT__Basics_LF_Basics_bool__rec (motive := fun _ => Original_LF__DOT__Basics_LF_Basics_grade)
          (Original_LF__DOT__Basics_LF_Basics_lower__grade g)
          (Original_LF__DOT__Basics_LF_Basics_bool__rec (motive := fun _ => Original_LF__DOT__Basics_LF_Basics_grade)
            (Original_LF__DOT__Basics_LF_Basics_lower__grade (Original_LF__DOT__Basics_LF_Basics_lower__grade g))
            (Original_LF__DOT__Basics_LF_Basics_lower__grade (Original_LF__DOT__Basics_LF_Basics_lower__grade (Original_LF__DOT__Basics_LF_Basics_lower__grade g)))
            (Original_LF__DOT__Basics_LF_Basics_ltb late_days (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))))))))))))))))))))
          (Original_LF__DOT__Basics_LF_Basics_ltb late_days (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))))))))))))))))
        (Original_LF__DOT__Basics_LF_Basics_ltb late_days (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))))))))
