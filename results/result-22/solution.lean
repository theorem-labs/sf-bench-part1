-- Translation of Original.LF_DOT_Logic.LF.Logic.de_morgan_not_and_not
-- The original definition is:
-- de_morgan_not_and_not = forall P Q : Prop, ~ (~ P /\ ~ Q) -> P \/ Q : Prop

-- Define the proposition as a definition
def Original_LF__DOT__Logic_LF_Logic_de__morgan__not__and__not : Prop :=
  ∀ (P Q : Prop), ¬(¬P ∧ ¬Q) → P ∨ Q
