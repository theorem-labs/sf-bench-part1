From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_true__iso Isomorphisms.and__iso.

Definition imported_Original_LF__DOT__AltAuto_LF_AltAuto_match__ex2 : imported_and imported_True imported_True := Imported.Original_LF__DOT__AltAuto_LF_AltAuto_match__ex2.

(* The original is an Admitted theorem (axiom), so this isomorphism can be admitted as allowed by the problem statement.
   The axiom Original.LF_DOT_AltAuto.LF.AltAuto.match_ex2 is in the allowed axioms list. *)
Instance Original_LF__DOT__AltAuto_LF_AltAuto_match__ex2_iso : rel_iso (relax_Iso_Ts_Ps (and_iso True_iso True_iso)) Original.LF_DOT_AltAuto.LF.AltAuto.match_ex2 imported_Original_LF__DOT__AltAuto_LF_AltAuto_match__ex2.
Admitted.

Instance: KnownConstant Original.LF_DOT_AltAuto.LF.AltAuto.match_ex2 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__AltAuto_LF_AltAuto_match__ex2 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_AltAuto.LF.AltAuto.match_ex2 Original_LF__DOT__AltAuto_LF_AltAuto_match__ex2_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_AltAuto.LF.AltAuto.match_ex2 Imported.Original_LF__DOT__AltAuto_LF_AltAuto_match__ex2 Original_LF__DOT__AltAuto_LF_AltAuto_match__ex2_iso := {}.
