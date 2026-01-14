/-
  Lean translation of not_implies_our_not from LF.Logic

  Original Rocq definition:
    Theorem not_implies_our_not : forall (P:Prop), ~ P -> (forall (Q:Prop), P -> Q).
    Proof. Admitted.
-/

-- Logic.not equivalent: negation as P -> False
def Logic_not (P : Prop) : Prop := P → _root_.False

-- not_implies_our_not as an axiom (since the original is Admitted)
axiom Original_LF__DOT__Logic_LF_Logic_not__implies__our__not : 
  ∀ (P : Prop), Logic_not P → ∀ (Q : Prop), P → Q
