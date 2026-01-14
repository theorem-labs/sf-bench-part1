-- Translation of bin type from Original.v
inductive Original_LF__DOT__Induction_LF_Induction_bin : Type where
  | Z : Original_LF__DOT__Induction_LF_Induction_bin
  | B0 (n : Original_LF__DOT__Induction_LF_Induction_bin) : Original_LF__DOT__Induction_LF_Induction_bin
  | B1 (n : Original_LF__DOT__Induction_LF_Induction_bin) : Original_LF__DOT__Induction_LF_Induction_bin

-- Translation of incr - axiom since it's Admitted in Original.v
axiom Original_LF__DOT__Induction_LF_Induction_incr : Original_LF__DOT__Induction_LF_Induction_bin → Original_LF__DOT__Induction_LF_Induction_bin

-- Translation of double_bin - axiom since it's Admitted in Original.v
axiom Original_LF__DOT__Induction_LF_Induction_double__bin : Original_LF__DOT__Induction_LF_Induction_bin → Original_LF__DOT__Induction_LF_Induction_bin

-- Translation of eq (equality) - define in Prop to export as SProp
inductive Corelib_Init_Logic_eq {X : Type} : X → X → Prop where
  | refl (x : X) : Corelib_Init_Logic_eq x x

-- Translation of double_incr_bin lemma - axiom since it's Admitted in Original.v
axiom Original_LF__DOT__Induction_LF_Induction_double__incr__bin : ∀ (b : Original_LF__DOT__Induction_LF_Induction_bin),
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__Induction_LF_Induction_double__bin (Original_LF__DOT__Induction_LF_Induction_incr b))
    (Original_LF__DOT__Induction_LF_Induction_incr (Original_LF__DOT__Induction_LF_Induction_incr (Original_LF__DOT__Induction_LF_Induction_double__bin b)))

-- True type (use built-in True)
def imported_True : Prop := _root_.True
