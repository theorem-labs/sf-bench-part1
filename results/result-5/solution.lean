-- Lean 4 translation of auto_example_1
-- Original: forall (P Q R: Prop), (P -> Q) -> (Q -> R) -> P -> R
-- This is Admitted in the original, so we use an axiom

set_option autoImplicit false

-- auto_example_1: forall (P Q R: Prop), (P -> Q) -> (Q -> R) -> P -> R
-- This is a simple transitivity/composition of implications
axiom Original_LF__DOT__Auto_LF_Auto_auto__example__1 : 
  ∀ (P Q R : Prop), (P → Q) → (Q → R) → P → R
