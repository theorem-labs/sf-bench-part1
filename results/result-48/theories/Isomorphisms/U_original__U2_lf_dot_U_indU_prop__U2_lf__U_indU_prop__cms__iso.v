From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__clos____refl____trans__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__cs__iso.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_cms : imported_nat -> imported_nat -> SProp := Imported.Original_LF__DOT__IndProp_LF_IndProp_cms.

Instance Original_LF__DOT__IndProp_LF_IndProp_cms_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 -> forall (x3 : nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> Iso (Original.LF_DOT_IndProp.LF.IndProp.cms x1 x3) (imported_Original_LF__DOT__IndProp_LF_IndProp_cms x2 x4).
Proof.
  intros n1 n2 Hn m1 m2 Hm.
  unfold Original.LF_DOT_IndProp.LF.IndProp.cms, imported_Original_LF__DOT__IndProp_LF_IndProp_cms.
  (* cms n m := clos_refl_trans cs n m *)
  apply (@Original_LF__DOT__IndProp_LF_IndProp_clos__refl__trans_iso nat imported_nat nat_iso).
  - intros a1 a2 Ha b1 b2 Hb.
    apply Original_LF__DOT__IndProp_LF_IndProp_cs_iso; assumption.
  - exact Hn.
  - exact Hm.
Defined.
Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.cms := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_cms := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.cms Original_LF__DOT__IndProp_LF_IndProp_cms_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.cms Imported.Original_LF__DOT__IndProp_LF_IndProp_cms Original_LF__DOT__IndProp_LF_IndProp_cms_iso := {}.