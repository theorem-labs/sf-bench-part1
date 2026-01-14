From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Original_LF__DOT__AltAuto_LF_AltAuto_match__ex1 : imported_True := Imported.Original_LF__DOT__AltAuto_LF_AltAuto_match__ex1.
Instance Original_LF__DOT__AltAuto_LF_AltAuto_match__ex1_iso : rel_iso {| to := True_iso; from := from True_iso; to_from := fun x : imported_True => to_from True_iso x; from_to := fun x : True => seq_p_of_t (from_to True_iso x) |}
    Original.LF_DOT_AltAuto.LF.AltAuto.match_ex1 imported_Original_LF__DOT__AltAuto_LF_AltAuto_match__ex1.
Proof.
  unfold rel_iso.
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_AltAuto.LF.AltAuto.match_ex1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__AltAuto_LF_AltAuto_match__ex1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_AltAuto.LF.AltAuto.match_ex1 Original_LF__DOT__AltAuto_LF_AltAuto_match__ex1_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_AltAuto.LF.AltAuto.match_ex1 Imported.Original_LF__DOT__AltAuto_LF_AltAuto_match__ex1 Original_LF__DOT__AltAuto_LF_AltAuto_match__ex1_iso := {}.