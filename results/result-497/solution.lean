-- Lean translation for one_church_peano and dependencies
prelude

-- True in Prop (becomes SProp after import)
inductive PTrue : Prop where
  | intro : PTrue

def True : Prop := PTrue

-- Equality in Prop (becomes SProp after import) - for Type
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality in Prop for Prop arguments (becomes SProp after import)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Church numerals type (cnat)
def Original_LF__DOT__Poly_LF_Poly_Exercises_cnat : Type 1 := 
  ∀ (X : Type), (X → X) → X → X

-- one : cnat  (applies f once)
def Original_LF__DOT__Poly_LF_Poly_Exercises_one : ∀ (X : Type), (X → X) → X → X :=
  fun X f x => f x

-- one_church_peano is Admitted in the original, so we use an axiom
axiom Original_LF__DOT__Poly_LF_Poly_Exercises_one__church__peano : 
  @Corelib_Init_Logic_eq nat
    (Original_LF__DOT__Poly_LF_Poly_Exercises_one nat S _0)
    (S _0)
