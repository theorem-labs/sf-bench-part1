-- Lean 4 translation for LF.Basics types and test_grade_comparison4

-- Equality in Prop (which imports as SProp in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality for Prop arguments (also imports as SProp → SProp → SProp in Rocq)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- True as an alias for Lean's True (will be exported to SProp)
def MyTrue : Prop := _root_.True

-- letter type: A, B, C, D, F
inductive Original_LF__DOT__Basics_LF_Basics_letter : Type where
  | A : Original_LF__DOT__Basics_LF_Basics_letter
  | B : Original_LF__DOT__Basics_LF_Basics_letter
  | C : Original_LF__DOT__Basics_LF_Basics_letter
  | D : Original_LF__DOT__Basics_LF_Basics_letter
  | F : Original_LF__DOT__Basics_LF_Basics_letter

-- Individual letter constructors  
def Original_LF__DOT__Basics_LF_Basics_A : Original_LF__DOT__Basics_LF_Basics_letter :=
  Original_LF__DOT__Basics_LF_Basics_letter.A

def Original_LF__DOT__Basics_LF_Basics_B : Original_LF__DOT__Basics_LF_Basics_letter :=
  Original_LF__DOT__Basics_LF_Basics_letter.B

def Original_LF__DOT__Basics_LF_Basics_C : Original_LF__DOT__Basics_LF_Basics_letter :=
  Original_LF__DOT__Basics_LF_Basics_letter.C

def Original_LF__DOT__Basics_LF_Basics_D : Original_LF__DOT__Basics_LF_Basics_letter :=
  Original_LF__DOT__Basics_LF_Basics_letter.D

def Original_LF__DOT__Basics_LF_Basics_F : Original_LF__DOT__Basics_LF_Basics_letter :=
  Original_LF__DOT__Basics_LF_Basics_letter.F

-- modifier type: Plus, Natural, Minus
inductive Original_LF__DOT__Basics_LF_Basics_modifier : Type where
  | Plus : Original_LF__DOT__Basics_LF_Basics_modifier
  | Natural : Original_LF__DOT__Basics_LF_Basics_modifier
  | Minus : Original_LF__DOT__Basics_LF_Basics_modifier

-- Individual modifier constructors
def Original_LF__DOT__Basics_LF_Basics_Plus : Original_LF__DOT__Basics_LF_Basics_modifier :=
  Original_LF__DOT__Basics_LF_Basics_modifier.Plus

def Original_LF__DOT__Basics_LF_Basics_Natural : Original_LF__DOT__Basics_LF_Basics_modifier :=
  Original_LF__DOT__Basics_LF_Basics_modifier.Natural

def Original_LF__DOT__Basics_LF_Basics_Minus : Original_LF__DOT__Basics_LF_Basics_modifier :=
  Original_LF__DOT__Basics_LF_Basics_modifier.Minus

-- grade type: Grade letter modifier
inductive Original_LF__DOT__Basics_LF_Basics_grade : Type where
  | Grade : Original_LF__DOT__Basics_LF_Basics_letter → Original_LF__DOT__Basics_LF_Basics_modifier → Original_LF__DOT__Basics_LF_Basics_grade

-- Grade constructor
def Original_LF__DOT__Basics_LF_Basics_Grade : Original_LF__DOT__Basics_LF_Basics_letter → Original_LF__DOT__Basics_LF_Basics_modifier → Original_LF__DOT__Basics_LF_Basics_grade :=
  Original_LF__DOT__Basics_LF_Basics_grade.Grade

-- comparison type: Eq, Lt, Gt
inductive Original_LF__DOT__Basics_LF_Basics_comparison : Type where
  | Eq : Original_LF__DOT__Basics_LF_Basics_comparison
  | Lt : Original_LF__DOT__Basics_LF_Basics_comparison
  | Gt : Original_LF__DOT__Basics_LF_Basics_comparison

-- Individual comparison constructors
def Original_LF__DOT__Basics_LF_Basics_Eq : Original_LF__DOT__Basics_LF_Basics_comparison :=
  Original_LF__DOT__Basics_LF_Basics_comparison.Eq

def Original_LF__DOT__Basics_LF_Basics_Lt : Original_LF__DOT__Basics_LF_Basics_comparison :=
  Original_LF__DOT__Basics_LF_Basics_comparison.Lt

def Original_LF__DOT__Basics_LF_Basics_Gt : Original_LF__DOT__Basics_LF_Basics_comparison :=
  Original_LF__DOT__Basics_LF_Basics_comparison.Gt

-- grade_comparison is an axiom (Admitted in Coq)
axiom Original_LF__DOT__Basics_LF_Basics_grade__comparison : 
  Original_LF__DOT__Basics_LF_Basics_grade → Original_LF__DOT__Basics_LF_Basics_grade → Original_LF__DOT__Basics_LF_Basics_comparison

-- test_grade_comparison4 is an axiom (Admitted in Coq)
-- It states: grade_comparison (Grade B Minus) (Grade C Plus) = Gt
axiom Original_LF__DOT__Basics_LF_Basics_test__grade__comparison4 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Basics_LF_Basics_grade__comparison
       (Original_LF__DOT__Basics_LF_Basics_Grade Original_LF__DOT__Basics_LF_Basics_B Original_LF__DOT__Basics_LF_Basics_Minus)
       (Original_LF__DOT__Basics_LF_Basics_Grade Original_LF__DOT__Basics_LF_Basics_C Original_LF__DOT__Basics_LF_Basics_Plus))
    Original_LF__DOT__Basics_LF_Basics_Gt
