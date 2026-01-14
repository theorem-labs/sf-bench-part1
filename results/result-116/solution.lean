prelude
-- Translation of definitions to be exported to Rocq
-- Prop in Lean gets exported to SProp in Rocq

-- True in Prop - will be exported to SProp
inductive True : Prop where
  | intro : True

-- Corelib_Init_Logic_eq in SProp (through Prop)
-- The interface expects SProp but we need Type for the main theorem
-- Let's use Prop for eq as well
inductive Corelib_Init_Logic_eq {X : Type} : X → X → Prop where
  | refl (x : X) : Corelib_Init_Logic_eq x x

-- Translation of eq_example1 - this is an admitted theorem
-- The interface expects the arguments to be Type-level eq
axiom Original_LF__DOT__AltAuto_LF_AltAuto_eq__example1 :
  ∀ (A B C : Type) (f : A → B) (g : B → C) (x : A) (y : B),
    Corelib_Init_Logic_eq y (f x) → Corelib_Init_Logic_eq (g y) (g (f x))
