-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

-- Polymorphic list type
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

-- Explicit definitions for nil and cons
def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

def Original_LF__DOT__Poly_LF_Poly_cons (X : Type) : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons

-- List append function
def Original_LF__DOT__Poly_LF_Poly_app {X : Type} : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X
  | Original_LF__DOT__Poly_LF_Poly_list.nil, l2 => l2
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t, l2 => Original_LF__DOT__Poly_LF_Poly_list.cons h (Original_LF__DOT__Poly_LF_Poly_app t l2)

-- subseq is an empty inductive type in Original.v (has no constructors)
-- We define it in Prop so it exports as SProp
inductive Original_LF__DOT__IndProp_LF_IndProp_subseq : Original_LF__DOT__Poly_LF_Poly_list nat → Original_LF__DOT__Poly_LF_Poly_list nat → Prop where

-- subseq_app is an admitted axiom in the Original.v file
axiom Original_LF__DOT__IndProp_LF_IndProp_subseq__app :
  (l1 : Original_LF__DOT__Poly_LF_Poly_list nat) →
  (l2 : Original_LF__DOT__Poly_LF_Poly_list nat) →
  (l3 : Original_LF__DOT__Poly_LF_Poly_list nat) →
  Original_LF__DOT__IndProp_LF_IndProp_subseq l1 l2 →
  Original_LF__DOT__IndProp_LF_IndProp_subseq l1 (Original_LF__DOT__Poly_LF_Poly_app l2 l3)
