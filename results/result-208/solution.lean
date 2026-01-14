-- Lean 4 translation for Original.LF.Rel.equivalence and all dependencies

-- relation type (must unfold to X -> X -> Prop)
def Original_LF_Rel_relation (X : Type) : Type := X -> X -> Prop

-- reflexive: forall a : X, R a a
def Original_LF_Rel_reflexive (X : Type) (R : X -> X -> Prop) : Prop :=
  forall a : X, R a a

-- symmetric: forall a b : X, R a b -> R b a
def Original_LF_Rel_symmetric (X : Type) (R : X -> X -> Prop) : Prop :=
  forall a b : X, R a b -> R b a

-- transitive: forall a b c : X, R a b -> R b c -> R a c
def Original_LF_Rel_transitive (X : Type) (R : X -> X -> Prop) : Prop :=
  forall a b c : X, R a b -> R b c -> R a c

-- equivalence: (reflexive R) /\ (symmetric R) /\ (transitive R)
def Original_LF_Rel_equivalence (X : Type) (R : X -> X -> Prop) : Prop :=
  Original_LF_Rel_reflexive X R ∧ Original_LF_Rel_symmetric X R ∧ Original_LF_Rel_transitive X R
