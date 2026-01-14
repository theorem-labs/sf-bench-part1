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

-- The app function (append)
def Original_LF__DOT__Poly_LF_Poly_app (X : Type) (l1 l2 : Original_LF__DOT__Poly_LF_Poly_list X) : Original_LF__DOT__Poly_LF_Poly_list X :=
  match l1 with
  | Original_LF__DOT__Poly_LF_Poly_list.nil => l2
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t => Original_LF__DOT__Poly_LF_Poly_list.cons h (Original_LF__DOT__Poly_LF_Poly_app X t l2)

-- The eq inductive type corresponding to Original.LF_DOT_ProofObjects.LF.ProofObjects.eq
inductive Original_LF__DOT__ProofObjects_LF_ProofObjects_eq {X : Type} : X → X → Prop where
  | eq_refl : ∀ (x : X), Original_LF__DOT__ProofObjects_LF_ProofObjects_eq x x

-- The singleton theorem: [] ++ [x] == [x]
def Original_LF__DOT__ProofObjects_LF_ProofObjects_singleton (X : Type) (x : X) : 
    Original_LF__DOT__ProofObjects_LF_ProofObjects_eq 
      (Original_LF__DOT__Poly_LF_Poly_app X (Original_LF__DOT__Poly_LF_Poly_nil X) (Original_LF__DOT__Poly_LF_Poly_cons X x (Original_LF__DOT__Poly_LF_Poly_nil X)))
      (Original_LF__DOT__Poly_LF_Poly_cons X x (Original_LF__DOT__Poly_LF_Poly_nil X)) :=
  Original_LF__DOT__ProofObjects_LF_ProofObjects_eq.eq_refl _
