/-
  Lean translation for iff and iff_trans from LF.Logic

  Original Rocq definitions:
    - iff : Prop -> Prop -> Prop  (P <-> Q)
    - iff_trans : forall P Q R : Prop, (P <-> Q) -> (Q <-> R) -> (P <-> R)
      (This is admitted in Original.v)
-/

-- Define iff as a structure matching how the importer expects it
structure iff (a b : Prop) : Prop where
  mp : a → b
  mpr : b → a

-- iff_trans: transitivity of iff (axiom since it's Admitted in Original.v)
axiom Original_LF__DOT__Logic_LF_Logic_iff__trans :
  ∀ (P Q R : Prop), iff P Q → iff Q R → iff P R
