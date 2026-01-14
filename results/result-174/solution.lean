-- Define our own list type (to avoid Lean stdlib issues)
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

-- Define aliases for nil and cons as separate definitions
def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

def Original_LF__DOT__Poly_LF_Poly_cons {X : Type} (h : X) (t : Original_LF__DOT__Poly_LF_Poly_list X) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons h t

-- Define our own equality type in Prop (will be exported as SProp)
inductive Original_LF__DOT__ProofObjects_LF_ProofObjects_eq {X : Type} : X → X → Prop where
  | eq_refl : ∀ x, Original_LF__DOT__ProofObjects_LF_ProofObjects_eq x x

-- The eq_cons axiom: cons preserves equality
axiom Original_LF__DOT__ProofObjects_LF_ProofObjects_eq__cons :
  {X : Type} → (h1 h2 : X) → (t1 t2 : Original_LF__DOT__Poly_LF_Poly_list X) →
  Original_LF__DOT__ProofObjects_LF_ProofObjects_eq h1 h2 →
  Original_LF__DOT__ProofObjects_LF_ProofObjects_eq t1 t2 →
  Original_LF__DOT__ProofObjects_LF_ProofObjects_eq 
    (Original_LF__DOT__Poly_LF_Poly_cons h1 t1) 
    (Original_LF__DOT__Poly_LF_Poly_cons h2 t2)
