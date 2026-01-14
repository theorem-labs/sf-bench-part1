-- Define iff in Prop so it exports to SProp in Rocq

-- iff as a structure so it becomes a record with primitive projections
structure iff (A B : Prop) : Prop where
  intro ::
  mp : A → B
  mpr : B → A

-- The main theorem is admitted in Original.v, so we declare it as an axiom
-- Original:
--   Lemma apply_iff_example1:
--     forall P Q R : Prop, (P <-> Q) -> (Q -> R) -> (P -> R).
--   Admitted.
axiom Original_LF__DOT__Logic_LF_Logic_apply__iff__example1 :
  ∀ (P Q R : Prop), iff P Q → (Q → R) → (P → R)
