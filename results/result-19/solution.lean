/-
  Lean translation of consequentia_mirabilis from LF.Logic

  Original Rocq definition:
    Definition consequentia_mirabilis := forall P:Prop, (~P -> P) -> P.
-/

-- The consequentia mirabilis (law of Clavius)
-- This is a Prop stating that for all P, if ~P implies P, then P holds.
def Original_LF__DOT__Logic_LF_Logic_consequentia__mirabilis : Prop :=
  ∀ (P : Prop), (¬P → P) → P
