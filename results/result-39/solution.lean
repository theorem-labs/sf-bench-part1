-- Translation of Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.or and or_elim

-- Define an inductive type for or (disjunction)
inductive Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or (P Q : Prop) : Prop where
  | or_introl : P → Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or P Q
  | or_intror : Q → Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or P Q

-- Define or_elim - elimination principle for disjunction
def Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or__elim 
  (P Q R : Prop) 
  (HPQ : Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or P Q) 
  (HPR : P → R) 
  (HQR : Q → R) : R :=
  match HPQ with
  | .or_introl HP => HPR HP
  | .or_intror HQ => HQR HQ
