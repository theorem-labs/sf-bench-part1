/-
  Lean translation of iff and iff_sym from LF.Logic

  Original Rocq definitions:
    Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).
    Theorem iff_sym : forall P Q : Prop, (P <-> Q) -> (Q <-> P). Admitted.
-/

-- iff as a structure in SProp (to match Rocq SProp import)
structure iff (P Q : Prop) : Prop where
  mp : P → Q
  mpr : Q → P

-- iff_sym as an axiom (since it's Admitted in the original)
axiom Original_LF__DOT__Logic_LF_Logic_iff__sym : ∀ (P Q : Prop), iff P Q → iff Q P
