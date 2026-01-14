-- Lean 4 translation for intuition_simplify2' and its dependencies

-- Define nat as an inductive type to match Rocq's nat
inductive nat : Type where
  | O : nat
  | S : nat -> nat

-- Define equality in Prop for Type arguments (becomes SProp when imported)
inductive Corelib_Init_Logic_eq {A : Type} : A -> A -> Prop where
  | refl : (a : A) -> Corelib_Init_Logic_eq a a

-- Define equality in Prop for Prop arguments (becomes SProp when imported)  
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A -> A -> Prop where
  | refl : (a : A) -> Corelib_Init_Logic_eq_Prop a a

-- Define and as a structure matching Rocq's and
structure and (A B : Prop) : Prop where
  intro ::
  left : A
  right : B

-- True in Prop - use a different internal name to avoid conflicts
inductive PTrue : Prop where
  | intro : PTrue

-- Alias for True - note we need to shadow the builtin
def True_ : Prop := PTrue

-- The main theorem - intuition_simplify2' is Admitted in Original.v
-- forall (x y : nat) (P Q : nat -> Prop), x = y /\ (P x -> Q x) /\ P x -> Q y
axiom Original_LF__DOT__AltAuto_LF_AltAuto_intuition__simplify2' :
  forall (x y : nat) (P Q : nat -> Prop),
    and (Corelib_Init_Logic_eq x y) (and (P x -> Q x) (P x)) -> Q y
