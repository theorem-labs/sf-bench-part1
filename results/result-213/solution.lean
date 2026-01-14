-- Lean translation for nor_not_and' and its dependencies

-- Internal definitions with unique names
namespace Internal

inductive MyFalse : Prop where

inductive MyAnd (a b : Prop) : Prop where
  | intro : a → b → MyAnd a b

end Internal

-- Create abbreviations that will be exported with the right names
abbrev False_ : Prop := Internal.MyFalse
abbrev and_ (a b : Prop) : Prop := Internal.MyAnd a b

-- Not is just negation
def Logic_not (P : Prop) : Prop := P → False_

-- nor inductive type
inductive Original_LF__DOT__AltAuto_LF_AltAuto_nor (P Q : Prop) : Prop where
  | stroke : Logic_not P → Logic_not Q → Original_LF__DOT__AltAuto_LF_AltAuto_nor P Q

-- nor_not_and' axiom (Admitted in Original.v)
axiom Original_LF__DOT__AltAuto_LF_AltAuto_nor__not__and' :
  ∀ (P Q : Prop), Original_LF__DOT__AltAuto_LF_AltAuto_nor P Q → and_ P Q → False_
