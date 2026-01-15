-- Lean translation for exp_3 and all dependencies
prelude

-- cnat type: forall X : Type, (X -> X) -> X -> X
def Original_LF__DOT__Poly_LF_Poly_Exercises_cnat : Type 1 := 
  (X : Type) → (X → X) → X → X

-- doit3times: applies f three times
def Original_LF__DOT__Poly_LF_Poly_doit3times (X : Type) (f : X → X) (n : X) : X :=
  f (f (f n))

-- one: cnat (applies f once)
def Original_LF__DOT__Poly_LF_Poly_Exercises_one : Original_LF__DOT__Poly_LF_Poly_Exercises_cnat :=
  fun _ f x => f x

-- two: cnat (applies f twice)
def Original_LF__DOT__Poly_LF_Poly_Exercises_two : Original_LF__DOT__Poly_LF_Poly_Exercises_cnat :=
  fun _ f x => f (f x)

-- three: cnat := @doit3times
def Original_LF__DOT__Poly_LF_Poly_Exercises_three : Original_LF__DOT__Poly_LF_Poly_Exercises_cnat :=
  Original_LF__DOT__Poly_LF_Poly_doit3times

-- plus is an axiom since it's Admitted in the original
axiom Original_LF__DOT__Poly_LF_Poly_Exercises_plus : 
  Original_LF__DOT__Poly_LF_Poly_Exercises_cnat → 
  Original_LF__DOT__Poly_LF_Poly_Exercises_cnat → 
  Original_LF__DOT__Poly_LF_Poly_Exercises_cnat

-- mult is an axiom since it's Admitted in the original
axiom Original_LF__DOT__Poly_LF_Poly_Exercises_mult : 
  Original_LF__DOT__Poly_LF_Poly_Exercises_cnat → 
  Original_LF__DOT__Poly_LF_Poly_Exercises_cnat → 
  Original_LF__DOT__Poly_LF_Poly_Exercises_cnat

-- exp is an axiom since it's Admitted in the original
axiom Original_LF__DOT__Poly_LF_Poly_Exercises_exp : 
  Original_LF__DOT__Poly_LF_Poly_Exercises_cnat → 
  Original_LF__DOT__Poly_LF_Poly_Exercises_cnat → 
  Original_LF__DOT__Poly_LF_Poly_Exercises_cnat

-- Equality in Prop (universe polymorphic)
inductive Corelib_Init_Logic_eq.{u} {A : Sort u} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- True as SProp (named "True" to match what checker expects)
inductive «True» : Prop where
  | intro : «True»

-- exp_3 is an axiom: exp three two = plus (mult two (mult two two)) one
-- It's Admitted in the original
axiom Original_LF__DOT__Poly_LF_Poly_Exercises_exp__3 : 
  @Corelib_Init_Logic_eq 
    Original_LF__DOT__Poly_LF_Poly_Exercises_cnat
    (Original_LF__DOT__Poly_LF_Poly_Exercises_exp 
      Original_LF__DOT__Poly_LF_Poly_Exercises_three 
      Original_LF__DOT__Poly_LF_Poly_Exercises_two)
    (Original_LF__DOT__Poly_LF_Poly_Exercises_plus 
      (Original_LF__DOT__Poly_LF_Poly_Exercises_mult 
        Original_LF__DOT__Poly_LF_Poly_Exercises_two 
        (Original_LF__DOT__Poly_LF_Poly_Exercises_mult 
          Original_LF__DOT__Poly_LF_Poly_Exercises_two 
          Original_LF__DOT__Poly_LF_Poly_Exercises_two)) 
      Original_LF__DOT__Poly_LF_Poly_Exercises_one)
