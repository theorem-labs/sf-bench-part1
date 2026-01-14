-- Lean 4 translation of Person, Sage, Moss, parent_of, clos_trans, ancestor_of, and ancestor_of_ex from Original.v

-- Person is an inductive type with 4 constructors
inductive Original_LF__DOT__IndProp_LF_IndProp_Person : Type where
  | Sage : Original_LF__DOT__IndProp_LF_IndProp_Person
  | Cleo : Original_LF__DOT__IndProp_LF_IndProp_Person
  | Ridley : Original_LF__DOT__IndProp_LF_IndProp_Person
  | Moss : Original_LF__DOT__IndProp_LF_IndProp_Person

-- Sage is the first constructor of Person
def Original_LF__DOT__IndProp_LF_IndProp_Sage : Original_LF__DOT__IndProp_LF_IndProp_Person :=
  Original_LF__DOT__IndProp_LF_IndProp_Person.Sage

-- Moss is the fourth constructor of Person
def Original_LF__DOT__IndProp_LF_IndProp_Moss : Original_LF__DOT__IndProp_LF_IndProp_Person :=
  Original_LF__DOT__IndProp_LF_IndProp_Person.Moss

-- clos_trans is the transitive closure of a relation
inductive Original_LF__DOT__IndProp_LF_IndProp_clos__trans {X : Type} (R : X → X → Prop) : X → X → Prop where
  | t_step (x y : X) : R x y → Original_LF__DOT__IndProp_LF_IndProp_clos__trans R x y
  | t_trans (x y z : X) : Original_LF__DOT__IndProp_LF_IndProp_clos__trans R x y → 
                          Original_LF__DOT__IndProp_LF_IndProp_clos__trans R y z → 
                          Original_LF__DOT__IndProp_LF_IndProp_clos__trans R x z

-- parent_of is an inductive predicate with 3 constructors
-- po_SC : parent_of Sage Cleo
-- po_SR : parent_of Sage Ridley  
-- po_CM : parent_of Cleo Moss
inductive Original_LF__DOT__IndProp_LF_IndProp_parent__of : Original_LF__DOT__IndProp_LF_IndProp_Person → Original_LF__DOT__IndProp_LF_IndProp_Person → Prop where
  | po_SC : Original_LF__DOT__IndProp_LF_IndProp_parent__of Original_LF__DOT__IndProp_LF_IndProp_Person.Sage Original_LF__DOT__IndProp_LF_IndProp_Person.Cleo
  | po_SR : Original_LF__DOT__IndProp_LF_IndProp_parent__of Original_LF__DOT__IndProp_LF_IndProp_Person.Sage Original_LF__DOT__IndProp_LF_IndProp_Person.Ridley
  | po_CM : Original_LF__DOT__IndProp_LF_IndProp_parent__of Original_LF__DOT__IndProp_LF_IndProp_Person.Cleo Original_LF__DOT__IndProp_LF_IndProp_Person.Moss

-- ancestor_of is defined as clos_trans parent_of
def Original_LF__DOT__IndProp_LF_IndProp_ancestor__of : Original_LF__DOT__IndProp_LF_IndProp_Person → Original_LF__DOT__IndProp_LF_IndProp_Person → Prop :=
  Original_LF__DOT__IndProp_LF_IndProp_clos__trans Original_LF__DOT__IndProp_LF_IndProp_parent__of

-- ancestor_of_ex is an Admitted axiom in Original.v that asserts ancestor_of Sage Moss
axiom Original_LF__DOT__IndProp_LF_IndProp_ancestor__of__ex : Original_LF__DOT__IndProp_LF_IndProp_ancestor__of Original_LF__DOT__IndProp_LF_IndProp_Sage Original_LF__DOT__IndProp_LF_IndProp_Moss
