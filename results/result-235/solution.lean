-- Lean translation for de_morgan_not_or and its dependencies

-- MyFalse: an empty inductive Prop  
inductive MyFalse : Prop where

-- MyAnd: conjunction
inductive MyAnd (a b : Prop) : Prop where
  | intro : a → b → MyAnd a b

-- MyOr: disjunction
inductive MyOr (a b : Prop) : Prop where
  | inl : a → MyOr a b
  | inr : b → MyOr a b

-- Aliases for export (these will become Imported.and, Imported.or in Rocq)
abbrev «and» := MyAnd
abbrev «or» := MyOr

-- Logic_not definition
def Logic_not (P : Prop) : Prop := P → MyFalse

-- Projections for MyAnd (needed by and_iso proof)
def a____at___U_original__U2_lf_dot_U_logic__U2_lf__U_logic__de____morgan____not____or__iso__hyg10 (a b : Prop) (p : MyAnd a b) : a :=
  match p with
  | MyAnd.intro x _ => x

def a____at___U_original__U2_lf_dot_U_logic__U2_lf__U_logic__de____morgan____not____or__iso__hyg12 (a b : Prop) (p : MyAnd a b) : b :=
  match p with
  | MyAnd.intro _ y => y

-- de_morgan_not_or theorem (axiomatized since Original.v has it Admitted)
axiom Original_LF__DOT__ProofObjects_LF_ProofObjects_de__morgan__not__or :
  ∀ (P Q : Prop), (MyOr P Q → MyFalse) → MyAnd (P → MyFalse) (Q → MyFalse)
