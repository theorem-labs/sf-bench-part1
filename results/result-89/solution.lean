-- Church numerals type
def Original_LF__DOT__Poly_LF_Poly_Exercises_cnat : Type 1 := 
  forall (X : Type), (X -> X) -> X -> X

-- zero' for Church numerals
def Original_LF__DOT__Poly_LF_Poly_Exercises_zero' : forall (X : Type), (X -> X) -> X -> X :=
  fun (X : Type) (succ : X -> X) (zero : X) => zero
