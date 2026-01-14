-- Translation of Rocq definitions for grade types and lower_grade

-- Equality in Prop (which imports as SProp in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- True as an alias for Lean's True (will be exported to SProp)
def MyTrue : Prop := _root_.True

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

-- Constructors exported as definitions
def Original_LF__DOT__Basics_LF_Basics_A : Original_LF__DOT__Basics_LF_Basics_letter := 
  Original_LF__DOT__Basics_LF_Basics_letter.A

def Original_LF__DOT__Basics_LF_Basics_Plus : Original_LF__DOT__Basics_LF_Basics_modifier := 
  Original_LF__DOT__Basics_LF_Basics_modifier.Plus

def Original_LF__DOT__Basics_LF_Basics_Natural : Original_LF__DOT__Basics_LF_Basics_modifier := 
  Original_LF__DOT__Basics_LF_Basics_modifier.Natural

def Original_LF__DOT__Basics_LF_Basics_Grade : Original_LF__DOT__Basics_LF_Basics_letter → Original_LF__DOT__Basics_LF_Basics_modifier → Original_LF__DOT__Basics_LF_Basics_grade :=
  Original_LF__DOT__Basics_LF_Basics_grade.Grade

-- lower_grade is an axiom (Admitted) in the original
axiom Original_LF__DOT__Basics_LF_Basics_lower__grade : Original_LF__DOT__Basics_LF_Basics_grade → Original_LF__DOT__Basics_LF_Basics_grade

-- lower_grade_A_Plus is also an axiom (Admitted) in the original
-- It states: lower_grade (Grade A Plus) = Grade A Natural
axiom Original_LF__DOT__Basics_LF_Basics_lower__grade__A__Plus : 
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__Basics_LF_Basics_lower__grade 
       (Original_LF__DOT__Basics_LF_Basics_Grade Original_LF__DOT__Basics_LF_Basics_A Original_LF__DOT__Basics_LF_Basics_Plus))
    (Original_LF__DOT__Basics_LF_Basics_Grade Original_LF__DOT__Basics_LF_Basics_A Original_LF__DOT__Basics_LF_Basics_Natural)
