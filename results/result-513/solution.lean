-- Lean translation for plus_2 and all dependencies

-- Equality in Prop (which imports as SProp in Rocq)
inductive Corelib_Init_Logic_eq {A : Sort u} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- True as an alias for Lean's True (will be exported to SProp)
def MyTrue : Prop := _root_.True

-- cnat type: forall X : Type, (X -> X) -> X -> X
-- Using abbrev to ensure it's definitionally equal to the expanded form
abbrev Original_LF__DOT__Poly_LF_Poly_Exercises_cnat : Type 1 := 
  (X : Type) → (X → X) → X → X

-- doit3times: applies f three times
def Original_LF__DOT__Poly_LF_Poly_doit3times (X : Type) (f : X → X) (n : X) : X :=
  f (f (f n))

-- two: forall X : Type, (X -> X) -> X -> X
def Original_LF__DOT__Poly_LF_Poly_Exercises_two : (X : Type) → (X → X) → X → X :=
  fun (X : Type) (f : X → X) (x : X) => f (f x)

-- three: forall X : Type, (X -> X) -> X -> X  
def Original_LF__DOT__Poly_LF_Poly_Exercises_three : (X : Type) → (X → X) → X → X :=
  Original_LF__DOT__Poly_LF_Poly_doit3times

-- plus is admitted in Rocq, so we declare it as an axiom
-- The type is: cnat -> cnat -> cnat = ((X : Type) → (X → X) → X → X) -> ((X : Type) → (X → X) → X → X) -> (X : Type) → (X → X) → X → X
axiom Original_LF__DOT__Poly_LF_Poly_Exercises_plus : 
  ((X : Type) → (X → X) → X → X) → 
  ((X : Type) → (X → X) → X → X) → 
  (X : Type) → (X → X) → X → X

-- plus_2 : plus two three = plus three two (an admitted theorem)
-- Using explicit type annotation to match the interface
axiom Original_LF__DOT__Poly_LF_Poly_Exercises_plus__2 :
  @Corelib_Init_Logic_eq ((X : Type) → (X → X) → X → X)
    (Original_LF__DOT__Poly_LF_Poly_Exercises_plus 
       Original_LF__DOT__Poly_LF_Poly_Exercises_two 
       Original_LF__DOT__Poly_LF_Poly_Exercises_three)
    (Original_LF__DOT__Poly_LF_Poly_Exercises_plus 
       Original_LF__DOT__Poly_LF_Poly_Exercises_three 
       Original_LF__DOT__Poly_LF_Poly_Exercises_two)
