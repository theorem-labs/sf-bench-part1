From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.__0__iso Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_evU_playground__ev__iso Isomorphisms.U_s__iso.

(* Prove that 100 and Imported.n100 are related by nat_iso *)
Lemma nat_100_iso : rel_iso nat_iso (100 : Datatypes.nat) Imported.n100.
Proof.
  unfold rel_iso. simpl.
  unfold Imported.n100.
  reflexivity.
Qed.

(* Build the Iso between ev 100 and imported_ev n100 *)
Definition ev_100_iso : Iso (Original.LF_DOT_IndProp.LF.IndProp.EvPlayground.ev (100 : Datatypes.nat))
                           (imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev Imported.n100) :=
  @Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev_iso (100 : Datatypes.nat) Imported.n100 nat_100_iso.

(* The imported ev100 is Imported.Original_LF__DOT__AltAuto_LF_AltAuto_ev100 *)
Definition imported_Original_LF__DOT__AltAuto_LF_AltAuto_ev100 : 
  imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev Imported.n100 :=
  Imported.Original_LF__DOT__AltAuto_LF_AltAuto_ev100.

(* Prove the isomorphism - both sides are in SProp so eq_refl works *)
Instance Original_LF__DOT__AltAuto_LF_AltAuto_ev100_iso : 
  rel_iso ev_100_iso Original.LF_DOT_AltAuto.LF.AltAuto.ev100 imported_Original_LF__DOT__AltAuto_LF_AltAuto_ev100.
Proof.
  unfold rel_iso.
  (* Both sides are in SProp, so eq is reflexive *)
  apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_AltAuto.LF.AltAuto.ev100 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__AltAuto_LF_AltAuto_ev100 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_AltAuto.LF.AltAuto.ev100 Original_LF__DOT__AltAuto_LF_AltAuto_ev100_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_AltAuto.LF.AltAuto.ev100 Imported.Original_LF__DOT__AltAuto_LF_AltAuto_ev100 Original_LF__DOT__AltAuto_LF_AltAuto_ev100_iso := {}.
