prelude

-- Translation of Corelib.Init.Logic.eq (equality) - define in Prop for SProp compatibility
inductive Corelib_Init_Logic_eq {X : Sort _} : X → X → Prop where
  | refl (x : X) : Corelib_Init_Logic_eq x x

-- Translation of True - no conflict in prelude mode
inductive True : Prop where
  | intro : True

-- eq_example1' is Admitted in the original, so we define it as an axiom
-- Original: forall (A B C : Type) (f : A -> B) (g : B -> C) (x : A) (y : B), y = f x -> g y = g (f x)
axiom Original_LF__DOT__AltAuto_LF_AltAuto_eq__example1' :
  ∀ (A B C : Sort _) (f : A → B) (g : B → C) (x : A) (y : B),
    Corelib_Init_Logic_eq y (f x) → Corelib_Init_Logic_eq (g y) (g (f x))
