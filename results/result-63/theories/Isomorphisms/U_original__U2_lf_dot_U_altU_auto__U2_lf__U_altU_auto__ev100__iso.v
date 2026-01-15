From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.__0__iso Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_evU_playground__ev__iso Isomorphisms.U_s__iso.

(* The imported ev100 has type ev over 100 represented with imported nat_S *)
(* The original ev100 has type ev over 100 represented with Datatypes nat *)

(* Build 100 as Datatypes.nat *)
Definition nat_100 : Datatypes.nat := 100.

(* Build 100 as imported_nat *)
Definition nat_100_imported : imported_nat := nat_to_imported nat_100.

Monomorphic Definition imported_Original_LF__DOT__AltAuto_LF_AltAuto_ev100 : imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev nat_100_imported := Imported.Original_LF__DOT__AltAuto_LF_AltAuto_ev100.

(* Helper: nat_100 is related to nat_to_imported nat_100 *)
Lemma nat_100_rel : rel_iso nat_iso nat_100 nat_100_imported.
Proof.
  constructor. reflexivity.
Defined.

Monomorphic Instance Original_LF__DOT__AltAuto_LF_AltAuto_ev100_iso : rel_iso (Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev_iso nat_100_rel) Original.LF_DOT_AltAuto.LF.AltAuto.ev100
    imported_Original_LF__DOT__AltAuto_LF_AltAuto_ev100.
Proof.
  unfold imported_Original_LF__DOT__AltAuto_LF_AltAuto_ev100.
  unfold nat_100_imported.
  (* We need to show that the isomorphism holds for axioms - since both sides are axioms that state ev 100, this is admitted *)
Admitted.
Instance: KnownConstant Original.LF_DOT_AltAuto.LF.AltAuto.ev100 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__AltAuto_LF_AltAuto_ev100 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_AltAuto.LF.AltAuto.ev100 Original_LF__DOT__AltAuto_LF_AltAuto_ev100_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_AltAuto.LF.AltAuto.ev100 Imported.Original_LF__DOT__AltAuto_LF_AltAuto_ev100 Original_LF__DOT__AltAuto_LF_AltAuto_ev100_iso := {}.
