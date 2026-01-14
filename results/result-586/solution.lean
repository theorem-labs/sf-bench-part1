-- Lean translation for mult_3 and dependencies
-- Using prelude to avoid name conflicts with True
prelude

-- Church numerals type (cnat)
def Original_LF__DOT__Poly_LF_Poly_Exercises_cnat : Type 1 := 
  ∀ (X : Type), (X → X) → X → X

-- doit3times applies f three times
def Original_LF__DOT__Poly_LF_Poly_doit3times {X : Type} (f : X → X) (n : X) : X :=
  f (f (f n))

-- two : cnat (applies f twice)
def Original_LF__DOT__Poly_LF_Poly_Exercises_two : ∀ (X : Type), (X → X) → X → X :=
  fun X f x => f (f x)

-- three : cnat := @doit3times
def Original_LF__DOT__Poly_LF_Poly_Exercises_three : ∀ (X : Type), (X → X) → X → X :=
  @Original_LF__DOT__Poly_LF_Poly_doit3times

-- plus is an axiom since it's Admitted in the original
axiom Original_LF__DOT__Poly_LF_Poly_Exercises_plus : 
  (∀ (X : Type), (X → X) → X → X) → 
  (∀ (X : Type), (X → X) → X → X) → 
  ∀ (X : Type), (X → X) → X → X

-- mult is an axiom since it's Admitted in the original
axiom Original_LF__DOT__Poly_LF_Poly_Exercises_mult : 
  (∀ (X : Type), (X → X) → X → X) → 
  (∀ (X : Type), (X → X) → X → X) → 
  ∀ (X : Type), (X → X) → X → X

-- Equality in Prop (will become SProp after import)
-- Universe polymorphic to handle different type levels
inductive Corelib_Init_Logic_eq.{u} {X : Sort u} : X → X → Prop where
  | refl (x : X) : Corelib_Init_Logic_eq x x

-- True in Prop (will become SProp after import)
inductive True : Prop where
  | intro : True

-- mult_3 is the theorem: mult two three = plus three three
-- It's Admitted in the original, so we use an axiom
axiom Original_LF__DOT__Poly_LF_Poly_Exercises_mult__3 : 
  @Corelib_Init_Logic_eq 
    (∀ (X : Type), (X → X) → X → X)
    (Original_LF__DOT__Poly_LF_Poly_Exercises_mult 
      Original_LF__DOT__Poly_LF_Poly_Exercises_two 
      Original_LF__DOT__Poly_LF_Poly_Exercises_three)
    (Original_LF__DOT__Poly_LF_Poly_Exercises_plus 
      Original_LF__DOT__Poly_LF_Poly_Exercises_three 
      Original_LF__DOT__Poly_LF_Poly_Exercises_three)
