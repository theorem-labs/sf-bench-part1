-- Export a custom True (will become SProp in Rocq Imported module)
-- We use MyTrue to avoid clash with Lean's True, then edit the .out file
inductive MyTrue : Prop where
  | intro : MyTrue

-- Translation of bin type from Original.v
inductive Original_LF__DOT__Induction_LF_Induction_bin : Type where
  | Z : Original_LF__DOT__Induction_LF_Induction_bin
  | B0 : Original_LF__DOT__Induction_LF_Induction_bin → Original_LF__DOT__Induction_LF_Induction_bin
  | B1 : Original_LF__DOT__Induction_LF_Induction_bin → Original_LF__DOT__Induction_LF_Induction_bin

-- Z constructor
def Original_LF__DOT__Induction_LF_Induction_Z : Original_LF__DOT__Induction_LF_Induction_bin :=
  Original_LF__DOT__Induction_LF_Induction_bin.Z

-- double_bin is Admitted in Rocq, so we use an axiom
axiom Original_LF__DOT__Induction_LF_Induction_double__bin : Original_LF__DOT__Induction_LF_Induction_bin → Original_LF__DOT__Induction_LF_Induction_bin

-- Translation of eq (equality) - define in Prop so it's imported as SProp
inductive Corelib_Init_Logic_eq {X : Type} : X → X → Prop where
  | refl (x : X) : Corelib_Init_Logic_eq x x

-- Translation of eq for Prop (will be imported as SProp -> SProp -> SProp)
inductive Corelib_Init_Logic_eq_Prop {X : Prop} : X → X → Prop where
  | refl (x : X) : Corelib_Init_Logic_eq_Prop x x

-- double_bin_zero is Admitted in Rocq, so we use an axiom
-- It states: double_bin Z = Z
axiom Original_LF__DOT__Induction_LF_Induction_double__bin__zero : 
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__Induction_LF_Induction_double__bin Original_LF__DOT__Induction_LF_Induction_Z) 
    Original_LF__DOT__Induction_LF_Induction_Z
