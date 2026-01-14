-- Lean 4 translation of the LF.Basics types

-- Equality in Prop (which imports as SProp in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- True as a Prop (renamed to avoid conflict with built-in True)
def MyTrue : Prop := _root_.True

-- letter type: A, B, C, D, F
inductive Original_LF__DOT__Basics_LF_Basics_letter : Type where
  | A : Original_LF__DOT__Basics_LF_Basics_letter
  | B : Original_LF__DOT__Basics_LF_Basics_letter
  | C : Original_LF__DOT__Basics_LF_Basics_letter
  | D : Original_LF__DOT__Basics_LF_Basics_letter
  | F : Original_LF__DOT__Basics_LF_Basics_letter

-- Shorthand constructors
def Original_LF__DOT__Basics_LF_Basics_A : Original_LF__DOT__Basics_LF_Basics_letter := Original_LF__DOT__Basics_LF_Basics_letter.A
def Original_LF__DOT__Basics_LF_Basics_B : Original_LF__DOT__Basics_LF_Basics_letter := Original_LF__DOT__Basics_LF_Basics_letter.B
def Original_LF__DOT__Basics_LF_Basics_C : Original_LF__DOT__Basics_LF_Basics_letter := Original_LF__DOT__Basics_LF_Basics_letter.C
def Original_LF__DOT__Basics_LF_Basics_D : Original_LF__DOT__Basics_LF_Basics_letter := Original_LF__DOT__Basics_LF_Basics_letter.D
def Original_LF__DOT__Basics_LF_Basics_F : Original_LF__DOT__Basics_LF_Basics_letter := Original_LF__DOT__Basics_LF_Basics_letter.F

-- modifier type: Plus, Natural, Minus
inductive Original_LF__DOT__Basics_LF_Basics_modifier : Type where
  | Plus : Original_LF__DOT__Basics_LF_Basics_modifier
  | Natural : Original_LF__DOT__Basics_LF_Basics_modifier
  | Minus : Original_LF__DOT__Basics_LF_Basics_modifier

-- Shorthand constructors
def Original_LF__DOT__Basics_LF_Basics_Plus : Original_LF__DOT__Basics_LF_Basics_modifier := Original_LF__DOT__Basics_LF_Basics_modifier.Plus
def Original_LF__DOT__Basics_LF_Basics_Natural : Original_LF__DOT__Basics_LF_Basics_modifier := Original_LF__DOT__Basics_LF_Basics_modifier.Natural
def Original_LF__DOT__Basics_LF_Basics_Minus : Original_LF__DOT__Basics_LF_Basics_modifier := Original_LF__DOT__Basics_LF_Basics_modifier.Minus

-- grade type: Grade letter modifier
inductive Original_LF__DOT__Basics_LF_Basics_grade : Type where
  | Grade : Original_LF__DOT__Basics_LF_Basics_letter → Original_LF__DOT__Basics_LF_Basics_modifier → Original_LF__DOT__Basics_LF_Basics_grade

-- Grade constructor
def Original_LF__DOT__Basics_LF_Basics_Grade : Original_LF__DOT__Basics_LF_Basics_letter → Original_LF__DOT__Basics_LF_Basics_modifier → Original_LF__DOT__Basics_LF_Basics_grade := Original_LF__DOT__Basics_LF_Basics_grade.Grade

-- comparison type: Eq, Lt, Gt
inductive Original_LF__DOT__Basics_LF_Basics_comparison : Type where
  | Eq : Original_LF__DOT__Basics_LF_Basics_comparison
  | Lt : Original_LF__DOT__Basics_LF_Basics_comparison
  | Gt : Original_LF__DOT__Basics_LF_Basics_comparison

-- Shorthand constructors
def Original_LF__DOT__Basics_LF_Basics_Eq : Original_LF__DOT__Basics_LF_Basics_comparison := Original_LF__DOT__Basics_LF_Basics_comparison.Eq
def Original_LF__DOT__Basics_LF_Basics_Lt : Original_LF__DOT__Basics_LF_Basics_comparison := Original_LF__DOT__Basics_LF_Basics_comparison.Lt
def Original_LF__DOT__Basics_LF_Basics_Gt : Original_LF__DOT__Basics_LF_Basics_comparison := Original_LF__DOT__Basics_LF_Basics_comparison.Gt

-- grade_comparison is an axiom (Admitted in Coq)
axiom Original_LF__DOT__Basics_LF_Basics_grade__comparison : 
  Original_LF__DOT__Basics_LF_Basics_grade → Original_LF__DOT__Basics_LF_Basics_grade → Original_LF__DOT__Basics_LF_Basics_comparison

-- lower_grade is an axiom (Admitted in Coq)
axiom Original_LF__DOT__Basics_LF_Basics_lower__grade : 
  Original_LF__DOT__Basics_LF_Basics_grade → Original_LF__DOT__Basics_LF_Basics_grade

-- lower_grade_lowers is an axiom (Admitted in Coq)
axiom Original_LF__DOT__Basics_LF_Basics_lower__grade__lowers : 
  ∀ (g : Original_LF__DOT__Basics_LF_Basics_grade),
    Corelib_Init_Logic_eq 
      (Original_LF__DOT__Basics_LF_Basics_grade__comparison 
        (Original_LF__DOT__Basics_LF_Basics_Grade Original_LF__DOT__Basics_LF_Basics_F Original_LF__DOT__Basics_LF_Basics_Minus) 
        g) 
      Original_LF__DOT__Basics_LF_Basics_Lt →
    Corelib_Init_Logic_eq 
      (Original_LF__DOT__Basics_LF_Basics_grade__comparison 
        (Original_LF__DOT__Basics_LF_Basics_lower__grade g) 
        g) 
      Original_LF__DOT__Basics_LF_Basics_Lt
