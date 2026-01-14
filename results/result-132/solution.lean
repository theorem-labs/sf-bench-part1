-- Use a namespace to avoid conflict with Lean's builtin False
namespace Rocq

-- False type (empty)
inductive False : Prop where

-- Existential type
inductive ex {A : Type} (P : A → Prop) : Prop where
  | intro (x : A) (h : P x) : ex P

-- Logic.not
def Logic_not (x : Prop) : Prop := x → Rocq.False

-- The dist_not_exists theorem is Admitted in Original.v, so we use an axiom
axiom Original_LF__DOT__Logic_LF_Logic_dist__not__exists : 
  ∀ (X : Type) (P : X → Prop), 
  (∀ x, P x) → 
  ex (fun x => Logic_not (P x)) → 
  Rocq.False

end Rocq
