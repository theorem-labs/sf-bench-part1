From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

Local Open Scope nat_scope.

From IsomorphismChecker Require Export Isomorphisms.__0__iso Isomorphisms.U_s__iso Isomorphisms.le__iso.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_test__le1 : imported_le (imported_S (imported_S (imported_S imported_0))) (imported_S (imported_S (imported_S imported_0))) := Imported.Original_LF__DOT__IndProp_LF_IndProp_test__le1.
Instance Original_LF__DOT__IndProp_LF_IndProp_test__le1_iso : rel_iso
    {|
      to := le_iso (S_iso (S_iso (S_iso _0_iso))) (S_iso (S_iso (S_iso _0_iso)));
      from := from (le_iso (S_iso (S_iso (S_iso _0_iso))) (S_iso (S_iso (S_iso _0_iso))));
      to_from :=
        fun x : imported_le (imported_S (imported_S (imported_S imported_0))) (imported_S (imported_S (imported_S imported_0))) =>
        to_from (le_iso (S_iso (S_iso (S_iso _0_iso))) (S_iso (S_iso (S_iso _0_iso)))) x;
      from_to := fun x : 3 <= 3 => seq_p_of_t (from_to (le_iso (S_iso (S_iso (S_iso _0_iso))) (S_iso (S_iso (S_iso _0_iso)))) x)
    |} Original.LF_DOT_IndProp.LF.IndProp.test_le1 imported_Original_LF__DOT__IndProp_LF_IndProp_test__le1.
Proof.
  unfold rel_iso. simpl.
  apply IsomorphismDefinitions.eq_refl.
Qed.
Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.test_le1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_test__le1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.test_le1 Original_LF__DOT__IndProp_LF_IndProp_test__le1_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.test_le1 Imported.Original_LF__DOT__IndProp_LF_IndProp_test__le1 Original_LF__DOT__IndProp_LF_IndProp_test__le1_iso := {}.