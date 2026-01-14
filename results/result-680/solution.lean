-- Translation of Rocq definitions for grade types, lower_grade, and lower_grade_F_Natural

-- True in SProp (the Rocq True is in Prop, but gets imported as SProp)
-- We use Lean's True here
abbrev True' := True

-- Corelib.Init.Logic.eq is just Eq in Lean
def Corelib_Init_Logic_eq {α : Sort u} (a b : α) : Prop := a = b

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

-- lower_grade is an axiom (Admitted) in the original
axiom Original_LF__DOT__Basics_LF_Basics_lower__grade : Original_LF__DOT__Basics_LF_Basics_grade → Original_LF__DOT__Basics_LF_Basics_grade

-- Aliases for constructor names
def Original_LF__DOT__Basics_LF_Basics_F : Original_LF__DOT__Basics_LF_Basics_letter := Original_LF__DOT__Basics_LF_Basics_letter.F
def Original_LF__DOT__Basics_LF_Basics_Natural : Original_LF__DOT__Basics_LF_Basics_modifier := Original_LF__DOT__Basics_LF_Basics_modifier.Natural
def Original_LF__DOT__Basics_LF_Basics_Minus : Original_LF__DOT__Basics_LF_Basics_modifier := Original_LF__DOT__Basics_LF_Basics_modifier.Minus
def Original_LF__DOT__Basics_LF_Basics_Grade := Original_LF__DOT__Basics_LF_Basics_grade.Grade

-- lower_grade_F_Natural is an axiom (Admitted) in the original
-- It states: lower_grade (Grade F Natural) = (Grade F Minus)
axiom Original_LF__DOT__Basics_LF_Basics_lower__grade__F__Natural : 
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__Basics_LF_Basics_lower__grade 
      (Original_LF__DOT__Basics_LF_Basics_Grade Original_LF__DOT__Basics_LF_Basics_F Original_LF__DOT__Basics_LF_Basics_Natural))
    (Original_LF__DOT__Basics_LF_Basics_Grade Original_LF__DOT__Basics_LF_Basics_F Original_LF__DOT__Basics_LF_Basics_Minus)
