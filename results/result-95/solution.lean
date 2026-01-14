-- Translation of ex, or, and dist_exists_or_term from Original.v

-- Existential type (Props.ex in Original.v)
inductive Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex {A : Type} (P : A -> Prop) : Prop where
  | ex_intro : forall x : A, P x -> Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex P

-- Disjunction type (Props.or in Original.v)
inductive Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or (P Q : Prop) : Prop where
  | or_introl : P → Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or P Q
  | or_intror : Q → Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or P Q

-- dist_exists_or_term: distributes existential over disjunction
def Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_dist__exists__or__term 
    (X : Type) (P Q : X -> Prop) :
    (Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex (fun x => Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or (P x) (Q x))) ->
    (Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or 
      (Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex (fun x => P x))
      (Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex (fun x => Q x))) :=
  fun H => match H with
    | Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex.ex_intro x Hx =>
        match Hx with
        | Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or.or_introl HPx => 
            Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or.or_introl 
              (Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex.ex_intro x HPx)
        | Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or.or_intror HQx => 
            Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or.or_intror 
              (Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex.ex_intro x HQx)
