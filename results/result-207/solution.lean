/-
  Lean translation for rtc_rsc_coincide and all dependencies
  
  Original Rocq definitions:
    Definition relation (X: Type) := X -> X -> Prop.
    
    Inductive clos_refl_trans {X : Type} (R : relation X) (x : X) : X -> Prop :=
      | rt_step (y : X) : R x y -> clos_refl_trans R x y
      | rt_refl : clos_refl_trans R x x
      | rt_trans (y z : X) : clos_refl_trans R x y -> clos_refl_trans R y z -> clos_refl_trans R x z.
    
    Inductive clos_refl_trans_1n {A : Type} (R : relation A) (x : A) : A -> Prop :=
      | rt1n_refl : clos_refl_trans_1n R x x
      | rt1n_trans (y z : A) (Hxy : R x y) (Hrest : clos_refl_trans_1n R y z) : clos_refl_trans_1n R x z.
    
    Theorem rtc_rsc_coincide :
      forall (X:Type) (R: relation X) (x y : X),
        clos_refl_trans R x y <-> clos_refl_trans_1n R x y.
    Proof. Admitted.
-/

set_option autoImplicit false

-- relation type
def Original_LF_Rel_relation (X : Type) : Type := X → X → Prop

-- clos_refl_trans: reflexive-transitive closure of a relation
inductive Original_LF_Rel_clos__refl__trans {X : Type} (R : X → X → Prop) : X → X → Prop where
  | rt_step (x y : X) : R x y → Original_LF_Rel_clos__refl__trans R x y
  | rt_refl (x : X) : Original_LF_Rel_clos__refl__trans R x x
  | rt_trans (x y z : X) : Original_LF_Rel_clos__refl__trans R x y → Original_LF_Rel_clos__refl__trans R y z → Original_LF_Rel_clos__refl__trans R x z

-- clos_refl_trans_1n: alternative reflexive-transitive closure
inductive Original_LF_Rel_clos__refl__trans__1n (A : Type) (R : A → A → Prop) : A → A → Prop where
  | rt1n_refl (x : A) : Original_LF_Rel_clos__refl__trans__1n A R x x
  | rt1n_trans (x y z : A) (Hxy : R x y) (Hrest : Original_LF_Rel_clos__refl__trans__1n A R y z) :
      Original_LF_Rel_clos__refl__trans__1n A R x z

-- iff (biconditional)
structure iff (A B : Prop) : Prop where
  mp : A → B
  mpr : B → A

-- rtc_rsc_coincide is an admitted axiom in the original
axiom Original_LF_Rel_rtc__rsc__coincide : ∀ (X : Type) (R : X → X → Prop) (x y : X),
  iff (Original_LF_Rel_clos__refl__trans R x y) (Original_LF_Rel_clos__refl__trans__1n X R x y)
