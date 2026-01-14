-- Lean translation of Rocq definitions for and_comm'

-- Define and in Prop (will map to SProp in Rocq)
structure and (A B : Prop) : Prop where
  intro ::
  fst : A
  snd : B

-- Define iff using and
def iff (A B : Prop) : Prop := and (A → B) (B → A)

-- Helper function: swaps components of an and
def Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__comm'__aux (P Q : Prop) (H : and P Q) : and Q P :=
  and.intro H.snd H.fst

-- Main theorem: P /\ Q <-> Q /\ P
def Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__comm' (P Q : Prop) : iff (and P Q) (and Q P) :=
  and.intro
    (Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__comm'__aux P Q)
    (Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__comm'__aux Q P)
