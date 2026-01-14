-- Lean 4 translation of Rocq nat, le, relation, reflexive, le_reflexive

-- Define nat as an inductive type to match Rocq's nat
inductive nat : Type where
  | O : nat
  | S : nat -> nat

-- Define le (less than or equal) as an inductive type to match Rocq's LF.IndProp.le
inductive Original_LF__DOT__IndProp_LF_IndProp_le : nat -> nat -> Prop where
  | le_n (n : nat) : Original_LF__DOT__IndProp_LF_IndProp_le n n
  | le_S (n m : nat) : Original_LF__DOT__IndProp_LF_IndProp_le n m -> Original_LF__DOT__IndProp_LF_IndProp_le n (nat.S m)

-- Define relation (must be universe polymorphic for import compatibility)
def Original_LF_Rel_relation (X : Type) : Type := X -> X -> Prop

-- Define reflexive
def Original_LF_Rel_reflexive (X : Type) (R : X -> X -> Prop) : Prop :=
  forall a : X, R a a

-- le_reflexive is an admitted theorem in Original.v
-- The type is: reflexive le, which expands to: forall a : nat, le a a
axiom Original_LF_Rel_le__reflexive : forall x : nat, Original_LF__DOT__IndProp_LF_IndProp_le x x
