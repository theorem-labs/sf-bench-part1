-- Translation of double_negation_elimination from Rocq to Lean 4

-- We need to ensure this exports as the same type as the Rocq original
-- The original is: forall P : Prop, ~ ~ P -> P
-- where ~ P = P -> False

-- Define our own negation to match Coq's exactly  
def Original_LF__DOT__Logic_LF_Logic_double__negation__elimination : Prop :=
  ∀ P : Prop, ((P → False) → False) → P
