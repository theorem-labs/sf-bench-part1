-- Translation for two_church_peano and its dependencies
-- Using prelude to avoid name conflicts
prelude

-- Equality in Prop (will become SProp when imported)
-- Universe polymorphic to handle different type levels
inductive Corelib_Init_Logic_eq.{u} {X : Sort u} : X → X → Prop where
  | refl (x : X) : Corelib_Init_Logic_eq x x

-- Equality specialized to Prop domain (becomes SProp -> SProp -> SProp when imported)
inductive Corelib_Init_Logic_eq_Prop {X : Prop} : X → X → Prop where
  | refl (x : X) : Corelib_Init_Logic_eq_Prop x x

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- True in Prop (will become SProp when imported)
inductive True : Prop where
  | intro : True

-- cnat := forall X : Type, (X -> X) -> X -> X
def Original_LF__DOT__Poly_LF_Poly_Exercises_cnat : Type 1 := 
  ∀ (X : Type), (X → X) → X → X

-- two : cnat := fun X f x => f (f x)
def Original_LF__DOT__Poly_LF_Poly_Exercises_two : ∀ (X : Type), (X → X) → X → X :=
  fun X f x => f (f x)

-- The theorem two nat S O = 2 is Admitted in the original
-- two nat S O computes to S (S O) which is 2, so this is trivially true
-- But since it's Admitted in the original, we translate it as an axiom
axiom Original_LF__DOT__Poly_LF_Poly_Exercises_two__church__peano : 
  @Corelib_Init_Logic_eq nat 
    (Original_LF__DOT__Poly_LF_Poly_Exercises_two nat (fun x => nat.S x) nat.O)
    (nat.S (nat.S nat.O))
