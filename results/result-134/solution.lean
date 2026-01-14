-- Stdlib False as an empty inductive proposition
inductive MyFalse : Prop where

-- Original.False is the same - also an empty proposition
inductive Original_False : Prop where

-- and as a structure so it becomes a record with primitive projections
structure MyAnd (A B : Prop) : Prop where
  intro ::
  fst : A
  snd : B

-- iff is (A -> B) /\ (B -> A)
def iff (A B : Prop) : Prop := MyAnd (A → B) (B → A)

-- Logic.not = fun x => x -> False
def Logic_not (x : Prop) : Prop := x → MyFalse

-- The not_equiv_false axiom (Admitted in Original.v)
axiom Original_LF__DOT__IndProp_LF_IndProp_not__equiv__false : 
  ∀ (P : Prop), (P → MyFalse) → iff P Original_False
