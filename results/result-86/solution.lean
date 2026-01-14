-- Church numerals definition
def Original_LF__DOT__Poly_LF_Poly_Exercises_cnat : Type 1 := 
  ∀ (X : Type), (X → X) → X → X

-- two' as a Church numeral
def Original_LF__DOT__Poly_LF_Poly_Exercises_two' : 
  ∀ (X : Type), (X → X) → X → X :=
  fun (X : Type) (succ : X → X) (zero : X) => succ (succ zero)
