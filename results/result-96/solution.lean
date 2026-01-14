-- Lean 4 translation for nor_comm' and all dependencies
set_option autoImplicit false

-- False (empty type in Prop) - renamed to avoid clash with Lean's False
inductive RocqFalse : Prop where

-- Logic.not (negation)
def Logic_not (P : Prop) : Prop := P → RocqFalse

-- iff (biconditional)
structure iff (A B : Prop) : Prop where
  mp : A → B
  mpr : B → A

-- nor: holds when both P and Q are false
inductive Original_LF__DOT__AltAuto_LF_AltAuto_nor (P Q : Prop) : Prop where
  | stroke : Logic_not P → Logic_not Q → Original_LF__DOT__AltAuto_LF_AltAuto_nor P Q

-- nor_comm': nor P Q <-> nor Q P
-- This is Admitted in Original.v, so we use axiom
axiom Original_LF__DOT__AltAuto_LF_AltAuto_nor__comm' :
  ∀ (P Q : Prop), iff (Original_LF__DOT__AltAuto_LF_AltAuto_nor P Q) (Original_LF__DOT__AltAuto_LF_AltAuto_nor Q P)
