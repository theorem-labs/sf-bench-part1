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

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le__3__5 : imported_le (imported_S (imported_S (imported_S imported_0))) (imported_S (imported_S (imported_S (imported_S (imported_S imported_0))))) := Imported.Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le__3__5.

(* The le_iso gives us an Iso between (3 <= 5)%nat and the imported le type *)
Definition le_3_5_iso_instance : Iso (Peano.le 3 5) (imported_le (imported_S (imported_S (imported_S imported_0))) (imported_S (imported_S (imported_S (imported_S (imported_S imported_0)))))).
Proof.
  exact (le_iso (S_iso (S_iso (S_iso _0_iso))) (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))).
Defined.

Instance Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le__3__5_iso : rel_iso
    le_3_5_iso_instance
    Original.LF_DOT_IndProp.LF.IndProp.LePlayground.le_3_5 
    imported_Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le__3__5.
Proof.
  unfold rel_iso, le_3_5_iso_instance.
  simpl.
  unfold imported_Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le__3__5.
  (* Both are inhabitants of an SProp, so they are equal *)
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.LePlayground.le_3_5 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le__3__5 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.LePlayground.le_3_5 Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le__3__5_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.LePlayground.le_3_5 Imported.Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le__3__5 Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le__3__5_iso := {}.