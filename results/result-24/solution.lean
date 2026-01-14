-- Lean 4 translation of Original.LF_DOT_AltAuto.LF.AltAuto.auto_example_3
-- This is an axiom in the original Rocq code

axiom Original_LF__DOT__AltAuto_LF_AltAuto_auto__example__3 :
  ∀ (P Q R S T U : Prop),
    (P → Q) → (Q → R) → (R → S) → (S → T) → (T → U) → P → U
