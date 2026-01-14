-- Church numerals and zero
-- cnat := forall X : Type, (X -> X) -> X -> X
-- zero := fun (X : Type) (_ : X -> X) (x : X) => x

-- Equality in Prop (so it becomes SProp when imported)
-- For Type arguments
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- For Prop arguments (becomes SProp -> SProp -> SProp when imported)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- True in Prop (will become SProp when imported)
namespace Exports

inductive True : Prop where
  | intro : True

end Exports

-- Define cnat as a type alias
def Original_LF__DOT__Poly_LF_Poly_Exercises_cnat : Type 1 := 
  (x : Type) → (x → x) → x → x

-- Define zero : cnat
def Original_LF__DOT__Poly_LF_Poly_Exercises_zero : 
  (x : Type) → (x → x) → x → x :=
  fun (X : Type) (_ : X → X) (x : X) => x

-- The theorem zero nat S O = 0 is admitted in the original
-- zero nat S O reduces to O, and 0 is also O, so this should be reflexivity
-- But since it's Admitted in original, we translate it as an axiom
axiom Original_LF__DOT__Poly_LF_Poly_Exercises_zero__church__peano : 
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__Poly_LF_Poly_Exercises_zero nat (fun x => nat.S x) nat.O)
    nat.O
