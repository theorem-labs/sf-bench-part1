-- Lean translation of Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.True and p_implies_true

-- True is an inductive type with one constructor I
inductive Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_True : Prop where
  | I : Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_True

-- p_implies_true is an axiom (Admitted in Rocq)
axiom Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_p__implies__true :
  ∀ (P : Type), P → Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_True
