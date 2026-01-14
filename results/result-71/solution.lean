-- Lean 4 translation of Original.LF_DOT_Poly.LF.Poly.MumbleGrumble definitions

-- Define nat to avoid universe issues
inductive Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_nat : Type where
  | O : Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_nat
  | S : Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_nat → Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_nat

-- The mumble inductive type
inductive Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble : Type where
  | a : Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble
  | b : Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble → Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_nat → Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble
  | c : Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble

-- The grumble inductive type (polymorphic in X)
inductive Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_grumble (X : Type) : Type where
  | d : Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble → Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_grumble X
  | e : X → Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_grumble X
