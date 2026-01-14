-- Lean translation of Original.LF_DOT_Logic.LF.Logic.peirce
-- peirce = forall P Q : Prop, ((P -> Q) -> P) -> P

def Original_LF__DOT__Logic_LF_Logic_peirce : Prop :=
  ∀ (P Q : Prop), ((P → Q) → P) → P
