From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.__0__iso Isomorphisms.U_s__iso Isomorphisms.le__iso.

(* test_le2: 3 <= 6, i.e., S (S (S O)) <= S (S (S (S (S (S O))))) *)
Monomorphic Definition imported_Original_LF__DOT__IndProp_LF_IndProp_test__le2 : imported_le (imported_S (imported_S (imported_S imported_0))) (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S imported_0)))))) := Imported.Original_LF__DOT__IndProp_LF_IndProp_test__le2.
Monomorphic Instance Original_LF__DOT__IndProp_LF_IndProp_test__le2_iso : rel_iso (le_iso (S_iso (S_iso (S_iso _0_iso))) (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))) Original.LF_DOT_IndProp.LF.IndProp.test_le2
    imported_Original_LF__DOT__IndProp_LF_IndProp_test__le2.
Admitted.
Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.test_le2 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_test__le2 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.test_le2 Original_LF__DOT__IndProp_LF_IndProp_test__le2_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.test_le2 Imported.Original_LF__DOT__IndProp_LF_IndProp_test__le2 Original_LF__DOT__IndProp_LF_IndProp_test__le2_iso := {}.