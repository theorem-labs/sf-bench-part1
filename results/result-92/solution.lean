/-
  Lean translation of clos_refl_trans_1n and rsc_trans from LF.Rel

  Original Rocq definitions:
    Definition relation (X: Type) := X -> X -> Prop.

    Inductive clos_refl_trans_1n {A : Type}
                                 (R : relation A) (x : A)
                                 : A -> Prop :=
      | rt1n_refl : clos_refl_trans_1n R x x
      | rt1n_trans (y z : A)
          (Hxy : R x y) (Hrest : clos_refl_trans_1n R y z) :
          clos_refl_trans_1n R x z.

    Lemma rsc_trans :
      forall (X:Type) (R: relation X) (x y z : X),
          clos_refl_trans_1n R x y  ->
          clos_refl_trans_1n R y z ->
          clos_refl_trans_1n R x z.
    Proof. Admitted.
-/

-- Definition of relation (exported as Original_LF_Rel_relation)
def Original_LF_Rel_relation (X : Type) : Type := X → X → Prop

-- Inductive clos_refl_trans_1n
-- Note: In Lean 4, we need to structure the inductive differently
-- The key is that y is not fixed but the recursion is on the starting point
inductive Original_LF_Rel_clos__refl__trans__1n (A : Type) (R : A → A → Prop) : A → A → Prop where
  | rt1n_refl (x : A) : Original_LF_Rel_clos__refl__trans__1n A R x x
  | rt1n_trans (x y z : A) (Hxy : R x y) (Hrest : Original_LF_Rel_clos__refl__trans__1n A R y z) :
      Original_LF_Rel_clos__refl__trans__1n A R x z

-- rsc_trans is an admitted axiom in the original
axiom Original_LF_Rel_rsc__trans : ∀ (X : Type) (R : X → X → Prop) (x y z : X),
  Original_LF_Rel_clos__refl__trans__1n X R x y →
  Original_LF_Rel_clos__refl__trans__1n X R y z →
  Original_LF_Rel_clos__refl__trans__1n X R x z
