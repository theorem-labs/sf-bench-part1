From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_logic__not__iso Isomorphisms.U_original__U2_lf_dot_U_altU_auto__U2_lf__U_altU_auto__nor__iso Isomorphisms.or__iso.

Definition imported_Original_LF__DOT__AltAuto_LF_AltAuto_nor__not__or : forall x x0 : SProp, imported_Original_LF__DOT__AltAuto_LF_AltAuto_nor x x0 -> imported_or x x0 -> imported_False := Imported.Original_LF__DOT__AltAuto_LF_AltAuto_nor__not__or.

(* This is an axiom isomorphism because nor_not_or is Admitted in Original.v *)
Instance Original_LF__DOT__AltAuto_LF_AltAuto_nor__not__or_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : Prop) (x4 : SProp) (hx0 : Iso x3 x4) (x5 : Original.LF_DOT_AltAuto.LF.AltAuto.nor x1 x3)
    (x6 : imported_Original_LF__DOT__AltAuto_LF_AltAuto_nor x2 x4),
  rel_iso (Original_LF__DOT__AltAuto_LF_AltAuto_nor_iso hx hx0) x5 x6 ->
  forall (x7 : x1 \/ x3) (x8 : imported_or x2 x4),
  rel_iso (relax_Iso_Ts_Ps (or_iso hx hx0)) x7 x8 ->
  rel_iso (relax_Iso_Ts_Ps False_iso) (Original.LF_DOT_AltAuto.LF.AltAuto.nor_not_or x1 x3 x5 x7) (imported_Original_LF__DOT__AltAuto_LF_AltAuto_nor__not__or x6 x8).
Proof.
  intros x1 x2 hx x3 x4 hx0 x5 x6 Hnor x7 x8 Hor.
  (* Both sides are in False/imported_False, which are empty types *)
  (* The result of nor_not_or is False, so we can match on it *)
  unfold rel_iso, relax_Iso_Ts_Ps, False_iso.
  simpl.
  (* rel_iso between two False values is always true *)
  constructor.
Defined.

Instance: KnownConstant Original.LF_DOT_AltAuto.LF.AltAuto.nor_not_or := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__AltAuto_LF_AltAuto_nor__not__or := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_AltAuto.LF.AltAuto.nor_not_or Original_LF__DOT__AltAuto_LF_AltAuto_nor__not__or_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_AltAuto.LF.AltAuto.nor_not_or Imported.Original_LF__DOT__AltAuto_LF_AltAuto_nor__not__or Original_LF__DOT__AltAuto_LF_AltAuto_nor__not__or_iso := {}.