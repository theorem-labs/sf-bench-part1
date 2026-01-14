-- Translation of auto_example_2 from LF.Auto

-- The original definition is Admitted in Rocq, so we use an axiom in Lean
axiom Original_LF__DOT__AltAuto_LF_AltAuto_auto__example__2 :
  ∀ (P Q R S T U : Prop),
    (P → Q) →
    (P → R) →
    (T → R) →
    (S → T → U) →
    ((P → Q) → P → S) →
    T →
    P →
    U
