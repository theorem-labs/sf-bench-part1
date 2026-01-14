-- Translation of or and or_commut from Original.v

-- Define 'or' as an alias for the standard Or
def or (P Q : Prop) : Prop := Or P Q

-- or_commut is admitted in Original.v, so we use an axiom
axiom Original_LF__DOT__Logic_LF_Logic_or__commut : ∀ (P Q : Prop), or P Q → or Q P
