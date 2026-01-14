-- Lean translation of Rocq definitions for booltree_ind_type_correct

-- Bool type (from LF.Basics) - same as Rocq stdlib bool
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

-- Booltree type (from LF.IndPrinciples)
-- Uses LF.Basics.bool which equals stdlib bool
inductive Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree : Type where
  | bt_empty : Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree
  | bt_leaf : Original_LF__DOT__Basics_LF_Basics_bool → Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree
  | bt_branch : Original_LF__DOT__Basics_LF_Basics_bool → Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree → Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree → Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree

-- The property type
def Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree__property__type : Type :=
  Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree → Prop

-- base_case is admitted in Original.v, so we use an axiom
axiom Original_LF__DOT__IndPrinciples_LF_IndPrinciples_base__case :
  (Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree → Prop) → Prop

-- leaf_case is admitted in Original.v, so we use an axiom
axiom Original_LF__DOT__IndPrinciples_LF_IndPrinciples_leaf__case :
  (Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree → Prop) → Prop

-- branch_case is admitted in Original.v, so we use an axiom
axiom Original_LF__DOT__IndPrinciples_LF_IndPrinciples_branch__case :
  (Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree → Prop) → Prop

-- booltree_ind_type is defined using the cases
def Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree__ind__type : Prop :=
  ∀ (P : Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree__property__type),
    Original_LF__DOT__IndPrinciples_LF_IndPrinciples_base__case P →
    Original_LF__DOT__IndPrinciples_LF_IndPrinciples_leaf__case P →
    Original_LF__DOT__IndPrinciples_LF_IndPrinciples_branch__case P →
    ∀ (b : Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree), P b

-- booltree_ind_type_correct is admitted in Original.v, so we use an axiom
axiom Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree__ind__type__correct :
  Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree__ind__type
