-- False type (empty) - will be exported as "False" in Rocq's Imported module
inductive MyFalse : Prop where

-- or type (disjunction) - will be exported as "or" in Rocq's Imported module
inductive MyOr (A B : Prop) : Prop where
  | or_introl : A → MyOr A B
  | or_intror : B → MyOr A B

-- Logic.not = fun x => x -> False
def Logic_not (x : Prop) : Prop := x → MyFalse

-- The excluded_middle_irrefutable theorem is Admitted in Original.v
-- It states: forall P, ~ ~ (P \/ ~ P)
-- Which expands to: forall P, ((P \/ (P -> False)) -> False) -> False
axiom Original_LF__DOT__Logic_LF_Logic_excluded__middle__irrefutable : 
  ∀ (P : Prop), (MyOr P (P → MyFalse) → MyFalse) → MyFalse
