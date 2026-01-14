-- Lean translation for de_morgan_not_or and its dependencies

-- We need to export definitions with specific names that the Rocq checker expects.
-- Since False, and, or are reserved in Lean, we define inductives with different
-- names and then create type-level abbreviations.

-- Internal definitions with unique names
namespace Internal

inductive MyFalse : Prop where

inductive MyAnd (a b : Prop) : Prop where
  | intro : a → b → MyAnd a b

inductive MyOr (a b : Prop) : Prop where
  | inl : a → MyOr a b
  | inr : b → MyOr a b

end Internal

-- Create abbreviations that will be exported with the right names
-- Note: We can't use False, and, or directly, so we use underscore suffix
-- and the Rocq side will need to define aliases

def False_ : Prop := Internal.MyFalse
def and_ (a b : Prop) : Prop := Internal.MyAnd a b
def or_ (a b : Prop) : Prop := Internal.MyOr a b

-- Not is just negation
def Logic_not (P : Prop) : Prop := P → False_

-- de_morgan_not_or theorem (axiomatized since Original.v has it Admitted)
axiom Original_LF__DOT__Logic_LF_Logic_de__morgan__not__or :
  ∀ (P Q : Prop), Logic_not (or_ P Q) → and_ (Logic_not P) (Logic_not Q)
