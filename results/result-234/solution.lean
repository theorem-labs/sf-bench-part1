-- Translation of required definitions for nor_not_or

-- False (empty proposition) - redefine (alias won't work with `False` reserved)
inductive MyFalse : Prop

-- Logic.not (negation)  
def Logic_not (P : Prop) : Prop := P → MyFalse

-- or (disjunction)
inductive «or» (P Q : Prop) : Prop where
  | inl : P → «or» P Q
  | inr : Q → «or» P Q

-- nor: holds when both P and Q are false
inductive Original_LF__DOT__AltAuto_LF_AltAuto_nor (P Q : Prop) : Prop where
  | stroke : Logic_not P → Logic_not Q → Original_LF__DOT__AltAuto_LF_AltAuto_nor P Q

-- nor_not_or: nor P Q implies not (P or Q)
-- This is an axiom in Original.v (Admitted)
axiom Original_LF__DOT__AltAuto_LF_AltAuto_nor__not__or :
  ∀ (P Q : Prop), Original_LF__DOT__AltAuto_LF_AltAuto_nor P Q → «or» P Q → MyFalse
