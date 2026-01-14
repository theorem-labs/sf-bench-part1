From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
From Stdlib Require Import ProofIrrelevance.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

From IsomorphismChecker Require Export Isomorphisms.U_false__iso.

Definition imported_Original_LF__DOT__AltAuto_LF_AltAuto_nor : SProp -> SProp -> SProp := Imported.Original_LF__DOT__AltAuto_LF_AltAuto_nor.

(* Build Iso between Original.nor x1 x3 and Imported.nor x2 x4 *)
Instance Original_LF__DOT__AltAuto_LF_AltAuto_nor_iso : (forall (x1 : Prop) (x2 : SProp) (hx1 : Iso x1 x2) (x3 : Prop) (x4 : SProp) (hx3 : Iso x3 x4),
   Iso (Original.LF_DOT_AltAuto.LF.AltAuto.nor x1 x3) (imported_Original_LF__DOT__AltAuto_LF_AltAuto_nor x2 x4)).
Proof.
  intros x1 x2 hx1 x3 x4 hx3.
  unfold imported_Original_LF__DOT__AltAuto_LF_AltAuto_nor.
  (* Original.nor x1 x3 has constructor: stroke : ~x1 -> ~x3 -> nor x1 x3
     Imported.nor x2 x4 has: stroke : Logic_not x2 -> Logic_not x4 -> nor x2 x4
     where Logic_not P = P -> False *)
  unshelve econstructor.
  - (* to: nor x1 x3 -> Imported.nor x2 x4 *)
    intro H. destruct H as [Hnp Hnq].
    (* Hnp : ~x1 = x1 -> Logic.False, Hnq : ~x3 = x3 -> Logic.False *)
    (* Need: Logic_not x2 = x2 -> Imported.False *)
    (* Need: Logic_not x4 = x4 -> Imported.False *)
    apply Imported.Original_LF__DOT__AltAuto_LF_AltAuto_nor_stroke.
    + (* x2 -> Imported.False *)
      intro h2. apply False_iso.(to). apply Hnp. apply hx1.(from). exact h2.
    + (* x4 -> Imported.False *)
      intro h4. apply False_iso.(to). apply Hnq. apply hx3.(from). exact h4.
  - (* from: Imported.nor x2 x4 -> nor x1 x3 *)
    intro H.
    apply Original.LF_DOT_AltAuto.LF.AltAuto.stroke.
    + (* ~x1 = x1 -> Logic.False *)
      intro h1. 
      apply False_iso.(from).
      apply (Imported.a____at___U_original__U2_lf_dot_U_altU_auto__U2_lf__U_altU_auto__nor____notSQUOTE__iso__hyg26 _ _ H).
      apply hx1.(to). exact h1.
    + (* ~x3 = x3 -> Logic.False *)
      intro h3.
      apply False_iso.(from).
      apply (Imported.a____at___U_original__U2_lf_dot_U_altU_auto__U2_lf__U_altU_auto__nor____notSQUOTE__iso__hyg29 _ _ H).
      apply hx3.(to). exact h3.
  - (* to_from: SProp proof irrelevance *)
    intro x. apply IsomorphismDefinitions.eq_refl.
  - (* from_to: Prop proof irrelevance *)
    intro x.
    assert (Heq : forall (p q : Original.LF_DOT_AltAuto.LF.AltAuto.nor x1 x3), IsomorphismDefinitions.eq p q).
    { intros p q. assert (p = q) by apply proof_irrelevance. subst. apply IsomorphismDefinitions.eq_refl. }
    apply Heq.
Defined.
Instance: KnownConstant Original.LF_DOT_AltAuto.LF.AltAuto.nor := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__AltAuto_LF_AltAuto_nor := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_AltAuto.LF.AltAuto.nor Original_LF__DOT__AltAuto_LF_AltAuto_nor_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_AltAuto.LF.AltAuto.nor Imported.Original_LF__DOT__AltAuto_LF_AltAuto_nor Original_LF__DOT__AltAuto_LF_AltAuto_nor_iso := {}.