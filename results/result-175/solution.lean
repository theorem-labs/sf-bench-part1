-- Lean 4 translation for Rocq nat and LF.Poly definitions

-- Define nat as an inductive type to match Rocq's nat
inductive nat : Type where
  | O : nat
  | S : nat -> nat

-- List inductive type corresponding to Original.LF_DOT_Poly.LF.Poly.list
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

-- The nil constructor
def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

-- mynil' := @nil nat
def Original_LF__DOT__Poly_LF_Poly_mynil' : Original_LF__DOT__Poly_LF_Poly_list nat :=
  Original_LF__DOT__Poly_LF_Poly_nil nat
