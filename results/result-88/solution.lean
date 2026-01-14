-- Lean translation of cnat and one' from Original.v

-- cnat is Church numerals: forall X : Type, (X -> X) -> X -> X
def Original_LF__DOT__Poly_LF_Poly_Exercises_cnat : Type 1 := 
  (x : Type) → (x → x) → x → x

-- one' : cnat := fun (X : Type) (succ : X -> X) (zero : X) => succ zero
def Original_LF__DOT__Poly_LF_Poly_Exercises_one' : Original_LF__DOT__Poly_LF_Poly_Exercises_cnat :=
  fun (x : Type) (succ : x → x) (zero : x) => succ zero
