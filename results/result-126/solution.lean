-- Lean translation for double_neg and dependencies

-- False type (empty type, no constructors)
-- Use Lean's built-in False with an alias
abbrev MyFalse : Prop := _root_.False

-- Not definition
def Logic_not (P : Prop) : Prop := P → MyFalse

-- Double negation axiom: P → ¬¬P
-- This is an axiom in the original Rocq code
axiom Original_LF__DOT__Logic_LF_Logic_double__neg : ∀ (P : Prop), P → Logic_not (Logic_not P)
