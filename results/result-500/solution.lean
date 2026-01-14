-- Lean translation for scc_3 and all dependencies
-- Using universe polymorphism to match Rocq's universe polymorphic definitions

universe u

-- Equality in Prop (which imports as SProp in Rocq) for Type elements
inductive Corelib_Init_Logic_eq {A : Type u} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality for Prop elements (imports as SProp in Rocq for SProp elements)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- True as an alias for Lean's True (will be exported to SProp)
def MyTrue : Prop := _root_.True

-- cnat type: forall X : Type u, (X -> X) -> X -> X
-- Universe polymorphic version
def Original_LF__DOT__Poly_LF_Poly_Exercises_cnat : Type (u + 1) := 
  (X : Type u) → (X → X) → X → X

-- doit3times: applies f three times
def Original_LF__DOT__Poly_LF_Poly_doit3times (X : Type u) (f : X → X) (n : X) : X :=
  f (f (f n))

-- two: cnat := fun X f x => f (f x)
def Original_LF__DOT__Poly_LF_Poly_Exercises_two : Original_LF__DOT__Poly_LF_Poly_Exercises_cnat :=
  fun (X : Type u) (f : X → X) (x : X) => f (f x)

-- three: cnat := @doit3times
def Original_LF__DOT__Poly_LF_Poly_Exercises_three : Original_LF__DOT__Poly_LF_Poly_Exercises_cnat :=
  Original_LF__DOT__Poly_LF_Poly_doit3times

-- scc is an axiom (admitted in Original)
axiom Original_LF__DOT__Poly_LF_Poly_Exercises_scc : 
  Original_LF__DOT__Poly_LF_Poly_Exercises_cnat → Original_LF__DOT__Poly_LF_Poly_Exercises_cnat

-- scc_3 is an axiom: scc two = three (admitted in Original)
axiom Original_LF__DOT__Poly_LF_Poly_Exercises_scc__3 :
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__Poly_LF_Poly_Exercises_scc Original_LF__DOT__Poly_LF_Poly_Exercises_two)
    Original_LF__DOT__Poly_LF_Poly_Exercises_three
