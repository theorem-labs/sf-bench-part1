/-
  Lean translation for provable_equiv_true

  Original Rocq definition:
    Lemma provable_equiv_true : forall (P : Prop), P -> (P <-> True).
    Admitted.
-/

-- We need to export True, True.intro, iff, etc
-- Use aliases to avoid name collision with Lean's True

-- MyTrue to avoid collision, will rename in output
inductive MyTrue : Prop where
  | intro : MyTrue

-- iff as a structure (to match how Rocq sees it)
structure iff (a b : Prop) : Prop where
  mp : a → b
  mpr : b → a

def mp (a b : Prop) (h : iff a b) : a → b := h.mp
def mpr (a b : Prop) (h : iff a b) : b → a := h.mpr
def iff_mk (a b : Prop) (mp : a → b) (mpr : b → a) : iff a b := iff.mk mp mpr

-- The axiom we need to translate
axiom Original_LF__DOT__IndProp_LF_IndProp_provable__equiv__true : ∀ (P : Prop), P → iff P MyTrue
