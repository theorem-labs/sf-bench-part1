-- Translation of False and ex_falso_quodlibet' from Original.v

-- Define False as an empty inductive type (in Prop)
inductive Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_False : Prop where

-- ex_falso_quodlibet' is an axiom: from False we can derive any Type
axiom Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex__falso__quodlibet' : 
  ∀ (P : Type), Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_False → P
