From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natlist__iso.

Definition imported_Original_LF__DOT__Lists_LF_Lists_NatList_app : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist -> imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist -> imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist := Imported.Original_LF__DOT__Lists_LF_Lists_NatList_app.

(* Helper lemma: app commutes with the isomorphism *)
Lemma app_commutes : forall l1 l2,
  IsomorphismDefinitions.eq 
    (natlist_to_imported (Original.LF_DOT_Lists.LF.Lists.NatList.app l1 l2))
    (Imported.Original_LF__DOT__Lists_LF_Lists_NatList_app (natlist_to_imported l1) (natlist_to_imported l2)).
Proof.
  fix IH 1.
  intros l1 l2. destruct l1 as [| n t]; simpl.
  - apply IsomorphismDefinitions.eq_refl.
  - apply (IsoEq.f_equal2 Imported.Original_LF__DOT__Lists_LF_Lists_NatList_natlist_cons).
    + apply IsomorphismDefinitions.eq_refl.
    + apply IH.
Qed.

Instance Original_LF__DOT__Lists_LF_Lists_NatList_app_iso : forall (x1 : Original.LF_DOT_Lists.LF.Lists.NatList.natlist) (x2 : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist),
  rel_iso Original_LF__DOT__Lists_LF_Lists_NatList_natlist_iso x1 x2 ->
  forall (x3 : Original.LF_DOT_Lists.LF.Lists.NatList.natlist) (x4 : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist),
  rel_iso Original_LF__DOT__Lists_LF_Lists_NatList_natlist_iso x3 x4 ->
  rel_iso Original_LF__DOT__Lists_LF_Lists_NatList_natlist_iso (Original.LF_DOT_Lists.LF.Lists.NatList.app x1 x3) (imported_Original_LF__DOT__Lists_LF_Lists_NatList_app x2 x4).
Proof.
  intros x1 x2 H12 x3 x4 H34.
  unfold rel_iso, imported_Original_LF__DOT__Lists_LF_Lists_NatList_app in *.
  simpl in *.
  eapply IsoEq.eq_trans.
  - apply app_commutes.
  - apply (IsoEq.f_equal2 Imported.Original_LF__DOT__Lists_LF_Lists_NatList_app H12 H34).
Defined.
Instance: KnownConstant Original.LF_DOT_Lists.LF.Lists.NatList.app := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Lists_LF_Lists_NatList_app := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.app Original_LF__DOT__Lists_LF_Lists_NatList_app_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.app Imported.Original_LF__DOT__Lists_LF_Lists_NatList_app Original_LF__DOT__Lists_LF_Lists_NatList_app_iso := {}.