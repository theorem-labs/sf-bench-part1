-- Translation of Rocq definitions to Lean 4

-- nat type
inductive nat : Type where
  | O : nat
  | S : nat → nat

-- List inductive type corresponding to Original.LF_DOT_Poly.LF.Poly.list
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

-- The nil constructor
def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

-- The cons constructor
def Original_LF__DOT__Poly_LF_Poly_cons (X : Type) (x : X) (l : Original_LF__DOT__Poly_LF_Poly_list X) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons x l

-- repeat''' function
def Original_LF__DOT__Poly_LF_Poly_repeat''' (X : Type) (x : X) (count : nat) : Original_LF__DOT__Poly_LF_Poly_list X :=
  match count with
  | nat.O => Original_LF__DOT__Poly_LF_Poly_list.nil
  | nat.S count' => Original_LF__DOT__Poly_LF_Poly_list.cons x (Original_LF__DOT__Poly_LF_Poly_repeat''' X x count')
