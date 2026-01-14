From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__le__iso.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_ge : imported_nat -> imported_nat -> SProp := Imported.Original_LF__DOT__IndProp_LF_IndProp_ge.

(* ge is defined as: ge m n := le n m *)
(* Original.LF_DOT_IndProp.LF.IndProp.ge x1 x3 = Original.LF_DOT_IndProp.LF.IndProp.le x3 x1 *)
(* Imported.Original_LF__DOT__IndProp_LF_IndProp_ge x2 x4 = Imported.Original_LF__DOT__IndProp_LF_IndProp_le x4 x2 *)

Instance Original_LF__DOT__IndProp_LF_IndProp_ge_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 -> forall (x3 : nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> Iso (Original.LF_DOT_IndProp.LF.IndProp.ge x1 x3) (imported_Original_LF__DOT__IndProp_LF_IndProp_ge x2 x4).
Proof.
  intros x1 x2 Hx1x2 x3 x4 Hx3x4.
  unfold Original.LF_DOT_IndProp.LF.IndProp.ge.
  unfold imported_Original_LF__DOT__IndProp_LF_IndProp_ge.
  unfold Imported.Original_LF__DOT__IndProp_LF_IndProp_ge.
  (* Now we need: Iso (Original.LF_DOT_IndProp.LF.IndProp.le x3 x1) (Imported.Original_LF__DOT__IndProp_LF_IndProp_le x4 x2) *)
  (* We have Original_LF__DOT__IndProp_LF_IndProp_le_iso for x3 x4 and x1 x2 *)
  apply Original_LF__DOT__IndProp_LF_IndProp_le_iso; assumption.
Defined.

Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.ge := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_ge := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.ge Original_LF__DOT__IndProp_LF_IndProp_ge_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.ge Imported.Original_LF__DOT__IndProp_LF_IndProp_ge Original_LF__DOT__IndProp_LF_IndProp_ge_iso := {}.