-- Translation of Original.LF_DOT_Poly.LF.Poly.list'

inductive Original_LF__DOT__Poly_LF_Poly_list' (X : Type) : Type where
  | nil' : Original_LF__DOT__Poly_LF_Poly_list' X
  | cons' : X → Original_LF__DOT__Poly_LF_Poly_list' X → Original_LF__DOT__Poly_LF_Poly_list' X
