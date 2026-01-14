-- Lean 4 translation for Original.LF.Rel.order and all dependencies

-- Equality in Prop (will be exported to SProp)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- True type in Prop (will be imported as SProp in Rocq)
-- Using True_ since True is a Lean builtin. Will rename in .out file.
inductive True_ : Prop where
  | intro : True_

-- relation type (must unfold to X -> X -> Prop)
def Original_LF_Rel_relation (X : Type) : Type := X -> X -> Prop

-- reflexive: forall a : X, R a a
def Original_LF_Rel_reflexive (X : Type) (R : X -> X -> Prop) : Prop :=
  forall a : X, R a a

-- transitive: forall a b c : X, R a b -> R b c -> R a c
def Original_LF_Rel_transitive (X : Type) (R : X -> X -> Prop) : Prop :=
  forall a b c : X, R a b -> R b c -> R a c

-- antisymmetric: forall a b : X, R a b -> R b a -> a = b
def Original_LF_Rel_antisymmetric (X : Type) (R : X -> X -> Prop) : Prop :=
  forall a b : X, R a b -> R b a -> Corelib_Init_Logic_eq a b

-- order: (reflexive R) /\ (antisymmetric R) /\ (transitive R)
-- In Lean, we define this as a structure/product
def Original_LF_Rel_order (X : Type) (R : X -> X -> Prop) : Prop :=
  Original_LF_Rel_reflexive X R ∧ Original_LF_Rel_antisymmetric X R ∧ Original_LF_Rel_transitive X R
