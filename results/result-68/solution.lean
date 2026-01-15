-- Lean translation for mult_2 and all dependencies
-- Using prelude to avoid name conflicts
-- NOT universe polymorphic - use fixed universes
prelude

-- Basic infrastructure needed in prelude mode
inductive Unit : Type where
  | unit : Unit

-- Equality in Prop (will become SProp after import)
-- NOT universe polymorphic - use Type 1 (the type of cnat)
inductive Corelib_Init_Logic_eq {X : Type 1} : X → X → Prop where
  | refl (x : X) : Corelib_Init_Logic_eq x x

-- True in Prop (will become SProp after import)
inductive True : Prop where
  | intro : True

-- SProp-sorted equality (for proving eq on SProp values)
inductive Corelib_Init_Logic_eq_Prop {X : Prop} : X → X → Prop where
  | refl (x : X) : Corelib_Init_Logic_eq_Prop x x

-- cnat type: forall X : Type, (X -> X) -> X -> X  
-- Fixed at Type 0 for X
def Original_LF__DOT__Poly_LF_Poly_Exercises_cnat : Type 1 := 
  (X : Type 0) → (X → X) → X → X

-- doit3times: applies f three times
def Original_LF__DOT__Poly_LF_Poly_doit3times (X : Type 0) (f : X → X) (n : X) : X :=
  f (f (f n))

-- three: cnat := @doit3times
def Original_LF__DOT__Poly_LF_Poly_Exercises_three : (X : Type 0) → (X → X) → X → X :=
  Original_LF__DOT__Poly_LF_Poly_doit3times

-- zero: cnat - identity on x, ignores f
def Original_LF__DOT__Poly_LF_Poly_Exercises_zero : (X : Type 0) → (X → X) → X → X :=
  fun (X : Type 0) (_f : X → X) (x : X) => x

-- plus is Admitted in Original.v, so we use an axiom
axiom Original_LF__DOT__Poly_LF_Poly_Exercises_plus : 
  ((X : Type 0) → (X → X) → X → X) → 
  ((X : Type 0) → (X → X) → X → X) → 
  (X : Type 0) → (X → X) → X → X

-- mult is Admitted in Original.v, so we use an axiom
axiom Original_LF__DOT__Poly_LF_Poly_Exercises_mult : 
  ((X : Type 0) → (X → X) → X → X) → 
  ((X : Type 0) → (X → X) → X → X) → 
  (X : Type 0) → (X → X) → X → X

-- mult_2 is Admitted in Original.v: mult zero (plus three three) = zero
axiom Original_LF__DOT__Poly_LF_Poly_Exercises_mult__2 : 
  @Corelib_Init_Logic_eq
    ((X : Type 0) → (X → X) → X → X)
    (fun (x2 : Type 0) (x4 : x2 → x2) (x6 : x2) =>
      Original_LF__DOT__Poly_LF_Poly_Exercises_mult
        (fun (x : Type 0) (x0 : x → x) (x1 : x) => Original_LF__DOT__Poly_LF_Poly_Exercises_zero x (fun x3 => x0 x3) x1)
        (fun (x : Type 0) (x0 : x → x) (x3 : x) =>
          Original_LF__DOT__Poly_LF_Poly_Exercises_plus
            (fun (x1 : Type 0) (x5 : x1 → x1) (x7 : x1) => Original_LF__DOT__Poly_LF_Poly_Exercises_three x1 (fun x8 => x5 x8) x7)
            (fun (x1 : Type 0) (x5 : x1 → x1) (x7 : x1) => Original_LF__DOT__Poly_LF_Poly_Exercises_three x1 (fun x8 => x5 x8) x7)
            x (fun x1 => x0 x1) x3)
        x2 (fun x => x4 x) x6)
    (fun (x2 : Type 0) (x4 : x2 → x2) (x6 : x2) => Original_LF__DOT__Poly_LF_Poly_Exercises_zero x2 (fun x => x4 x) x6)
