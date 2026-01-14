-- Lean 4 translation of Rocq nat, le, lt, and lt_trans'

-- Define nat as an inductive type to match Rocq's nat
inductive nat : Type where
  | O : nat
  | S : nat -> nat

-- Define le (less than or equal) as an inductive type to match Rocq's LF.IndProp.le
inductive Original_LF__DOT__IndProp_LF_IndProp_le : nat -> nat -> Prop where
  | le_n (n : nat) : Original_LF__DOT__IndProp_LF_IndProp_le n n
  | le_S (n m : nat) : Original_LF__DOT__IndProp_LF_IndProp_le n m -> Original_LF__DOT__IndProp_LF_IndProp_le n (nat.S m)

-- Define lt (less than) as in Rocq's LF.IndProp.lt
def Original_LF__DOT__IndProp_LF_IndProp_lt (n m : nat) : Prop :=
  Original_LF__DOT__IndProp_LF_IndProp_le (nat.S n) m

-- Define relation (must be universe polymorphic for import compatibility)
def Original_LF_Rel_relation (X : Type) : Type := X -> X -> Prop

-- Define transitive (note: uses explicit X argument like Rocq version)
def Original_LF_Rel_transitive (X : Type) (R : X -> X -> Prop) : Prop :=
  forall a b c : X, R a b -> R b c -> R a c

-- lt_trans' is an admitted theorem in Original.v
-- The type is: transitive lt, which expands to:
-- forall a b c : nat, lt a b -> lt b c -> lt a c
axiom Original_LF_Rel_lt__trans' : forall x x0 x1 : nat,
  Original_LF__DOT__IndProp_LF_IndProp_lt x x0 -> 
  Original_LF__DOT__IndProp_LF_IndProp_lt x0 x1 -> 
  Original_LF__DOT__IndProp_LF_IndProp_lt x x1
