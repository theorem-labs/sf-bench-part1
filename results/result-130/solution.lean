-- Lean translation for nor_not_and' and its dependencies

-- Custom False type
inductive MyFalse : Prop where

-- Custom And type
inductive MyAnd (a b : Prop) : Prop where
  | intro : a → b → MyAnd a b

-- Not is just negation
def Logic_not (P : Prop) : Prop := P → MyFalse

-- nor inductive type
inductive Original_LF__DOT__AltAuto_LF_AltAuto_nor (P Q : Prop) : Prop where
  | stroke : Logic_not P → Logic_not Q → Original_LF__DOT__AltAuto_LF_AltAuto_nor P Q

-- nor_not_and' axiom (Admitted in Original.v)
axiom Original_LF__DOT__AltAuto_LF_AltAuto_nor__not__and' :
  ∀ (P Q : Prop), Original_LF__DOT__AltAuto_LF_AltAuto_nor P Q → MyAnd P Q → MyFalse
