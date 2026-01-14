From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf__U_rel__relation__iso Interface.U_original__U2_lf__U_rel__order__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__le__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf__U_rel__relation__iso Interface.U_original__U2_lf__U_rel__order__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__le__iso.

  Export Interface.U_original__U2_lf__U_rel__relation__iso.CodeBlocks Interface.U_original__U2_lf__U_rel__order__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__le__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf__U_rel__relation__iso.Interface <+ Interface.U_original__U2_lf__U_rel__order__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__le__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF_Rel_le__order : imported_Original_LF_Rel_order (fun H H0 : imported_nat => imported_Original_LF__DOT__IndProp_LF_IndProp_le H H0).
Parameter Original_LF_Rel_le__order_iso : rel_iso
    {|
      to :=
        Original_LF_Rel_order_iso Original.LF_DOT_IndProp.LF.IndProp.le (fun H H0 : imported_nat => imported_Original_LF__DOT__IndProp_LF_IndProp_le H H0)
          (fun (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) => Original_LF__DOT__IndProp_LF_IndProp_le_iso hx hx0);
      from :=
        from
          (Original_LF_Rel_order_iso Original.LF_DOT_IndProp.LF.IndProp.le (fun H H0 : imported_nat => imported_Original_LF__DOT__IndProp_LF_IndProp_le H H0)
             (fun (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) => Original_LF__DOT__IndProp_LF_IndProp_le_iso hx hx0));
      to_from :=
        fun x : imported_Original_LF_Rel_order (fun H H0 : imported_nat => imported_Original_LF__DOT__IndProp_LF_IndProp_le H H0) =>
        to_from
          (Original_LF_Rel_order_iso Original.LF_DOT_IndProp.LF.IndProp.le (fun H H0 : imported_nat => imported_Original_LF__DOT__IndProp_LF_IndProp_le H H0)
             (fun (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) => Original_LF__DOT__IndProp_LF_IndProp_le_iso hx hx0))
          x;
      from_to :=
        fun x : Original.LF.Rel.order Original.LF_DOT_IndProp.LF.IndProp.le =>
        seq_p_of_t
          (from_to
             (Original_LF_Rel_order_iso Original.LF_DOT_IndProp.LF.IndProp.le (fun H H0 : imported_nat => imported_Original_LF__DOT__IndProp_LF_IndProp_le H H0)
                (fun (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) => Original_LF__DOT__IndProp_LF_IndProp_le_iso hx hx0))
             x)
    |} Original.LF.Rel.le_order imported_Original_LF_Rel_le__order.
Existing Instance Original_LF_Rel_le__order_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF.Rel.le_order ?x) => unify x Original_LF_Rel_le__order_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF.Rel.le_order imported_Original_LF_Rel_le__order ?x) => unify x Original_LF_Rel_le__order_iso; constructor : typeclass_instances.


End Interface.