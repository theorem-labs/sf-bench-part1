/-
  Lean translation of LF.Rel definitions:
  - relation
  - clos_refl_trans_1n
  - rsc_R (axiom)
-/

-- relation is just a binary relation on X
def Original_LF_Rel_relation (X : Type) : Type := X → X → Prop

-- Reflexive-transitive closure (1n form)
-- In Lean, we need both endpoints as indices, not just the second
inductive Original_LF_Rel_clos__refl__trans__1n {A : Type} 
    (R : A → A → Prop) : A → A → Prop where
  | rt1n_refl (x : A) : Original_LF_Rel_clos__refl__trans__1n R x x
  | rt1n_trans (x y z : A) (Hxy : R x y) (Hrest : Original_LF_Rel_clos__refl__trans__1n R y z) :
      Original_LF_Rel_clos__refl__trans__1n R x z

-- rsc_R is admitted in Rocq, so we make it an axiom
axiom Original_LF_Rel_rsc__R : ∀ (X : Type) (R : X → X → Prop) (x y : X),
  R x y → Original_LF_Rel_clos__refl__trans__1n R x y
