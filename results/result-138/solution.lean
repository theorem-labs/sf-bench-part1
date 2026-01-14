-- Lean translation for contradiction_implies_anything and its dependencies

-- MyFalse: an empty inductive Prop  
inductive MyFalse : Prop where

-- We need to export a "False" name for the Rocq checker
-- Use a namespace to avoid conflict with Lean's builtin False
namespace Exports
  def False : Prop := MyFalse
end Exports

-- MyAnd: conjunction
inductive MyAnd (a b : Prop) : Prop where
  | intro : a → b → MyAnd a b

-- Aliases for export
abbrev «and» := MyAnd

-- Logic_not definition
def Logic_not (P : Prop) : Prop := P → MyFalse

-- Projections for MyAnd (needed by and_iso proof)
def a____at___U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__de____morgan____not____or__iso__hyg10 (a b : Prop) (p : MyAnd a b) : a :=
  match p with
  | MyAnd.intro x _ => x

def a____at___U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__de____morgan____not____or__iso__hyg12 (a b : Prop) (p : MyAnd a b) : b :=
  match p with
  | MyAnd.intro _ y => y

-- contradiction_implies_anything theorem (axiomatized since Original.v has it Admitted)
axiom Original_LF__DOT__ProofObjects_LF_ProofObjects_contradiction__implies__anything :
  ∀ (P Q : Prop), (MyAnd P (P → MyFalse)) → Q
