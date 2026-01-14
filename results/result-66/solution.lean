-- Translation of Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.or and inj_l

-- Define an inductive type for or (disjunction)
inductive Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or (P Q : Prop) : Prop where
  | or_introl : P → Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or P Q
  | or_intror : Q → Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or P Q

-- Define inj_l as the left injection
def Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_inj__l (P Q : Prop) (HP : P) : Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or P Q :=
  Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or.or_introl HP
