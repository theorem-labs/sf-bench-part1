-- Lean translation of Rocq definitions

-- Define and, or, iff in Prop (will map to SProp in Rocq)
-- The key insight: we use structure for `and` which gets projections

structure and (A B : Prop) : Prop where
  intro ::
  fst : A
  snd : B

inductive or (A B : Prop) : Prop where
  | inl : A → or A B
  | inr : B → or A B

def iff (A B : Prop) : Prop := and (A → B) (B → A)

-- The main axiom: or distributes over and (from ProofObjects module)
axiom Original_LF__DOT__ProofObjects_LF_ProofObjects_or__distributes__over__and :
  ∀ (P Q R : Prop), iff (or P (and Q R)) (and (or P Q) (or P R))
