From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natlist__iso.
Import IsomorphismDefinitions.

Definition imported_Original_LF__DOT__Lists_LF_Lists_NatList_app : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist -> imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist -> imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist := Imported.Original_LF__DOT__Lists_LF_Lists_NatList_app.

(* Helper: Imported.app respects the cons constructor *)
Lemma imported_app_cons : forall n t l2,
  IsomorphismDefinitions.eq 
    (Imported.Original_LF__DOT__Lists_LF_Lists_NatList_app 
      (Imported.Original_LF__DOT__Lists_LF_Lists_NatList_natlist_cons n t) l2)
    (Imported.Original_LF__DOT__Lists_LF_Lists_NatList_natlist_cons n 
      (Imported.Original_LF__DOT__Lists_LF_Lists_NatList_app t l2)).
Proof.
  intros.
  apply IsomorphismDefinitions.eq_refl.
Qed.

(* First, we prove that app commutes with natlist_to_imported *)
Lemma app_commutes : forall (l1 l2 : Original.LF_DOT_Lists.LF.Lists.NatList.natlist),
  Logic.eq (natlist_to_imported (Original.LF_DOT_Lists.LF.Lists.NatList.app l1 l2))
           (Imported.Original_LF__DOT__Lists_LF_Lists_NatList_app (natlist_to_imported l1) (natlist_to_imported l2)).
Proof.
  fix IH 1.
  intros l1 l2.
  destruct l1 as [| n t].
  { reflexivity. }
  { simpl (Original.LF_DOT_Lists.LF.Lists.NatList.app _ _).
    simpl (natlist_to_imported (Original.LF_DOT_Lists.LF.Lists.NatList.cons _ _)).
    specialize (IH t l2) as IH_t.
    pose proof (seq_of_eq IH_t) as IH_seq.
    apply eq_of_seq.
    apply (f_equal (Imported.Original_LF__DOT__Lists_LF_Lists_NatList_natlist_cons (nat_to_imported n))) in IH_seq.
    pose proof (eq_sym (imported_app_cons (nat_to_imported n) (natlist_to_imported t) (natlist_to_imported l2))) as Happ.
    apply (eq_trans IH_seq Happ). }
Qed.

Instance Original_LF__DOT__Lists_LF_Lists_NatList_app_iso : forall (x1 : Original.LF_DOT_Lists.LF.Lists.NatList.natlist) (x2 : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist),
  rel_iso Original_LF__DOT__Lists_LF_Lists_NatList_natlist_iso x1 x2 ->
  forall (x3 : Original.LF_DOT_Lists.LF.Lists.NatList.natlist) (x4 : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist),
  rel_iso Original_LF__DOT__Lists_LF_Lists_NatList_natlist_iso x3 x4 ->
  rel_iso Original_LF__DOT__Lists_LF_Lists_NatList_natlist_iso (Original.LF_DOT_Lists.LF.Lists.NatList.app x1 x3) (imported_Original_LF__DOT__Lists_LF_Lists_NatList_app x2 x4).
Proof.
  intros x1 x2 H1 x3 x4 H2.
  unfold rel_iso in *.
  unfold imported_Original_LF__DOT__Lists_LF_Lists_NatList_app.
  unfold Original_LF__DOT__Lists_LF_Lists_NatList_natlist_iso in *.
  simpl in *.
  (* H1 : eq (natlist_to_imported x1) x2 *)
  (* H2 : eq (natlist_to_imported x3) x4 *)
  (* Goal: eq (natlist_to_imported (app x1 x3)) (Imported.app x2 x4) *)
  (* First: natlist_to_imported (app x1 x3) = Imported.app (natlist_to_imported x1) (natlist_to_imported x3) *)
  pose proof (seq_of_eq (app_commutes x1 x3)) as Hcomm.
  (* Then: Imported.app (natlist_to_imported x1) (natlist_to_imported x3) = Imported.app x2 x4 *)
  pose proof (f_equal2 Imported.Original_LF__DOT__Lists_LF_Lists_NatList_app H1 H2) as Hargs.
  apply (eq_trans Hcomm Hargs).
Defined.

Instance: KnownConstant Original.LF_DOT_Lists.LF.Lists.NatList.app := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Lists_LF_Lists_NatList_app := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.app Original_LF__DOT__Lists_LF_Lists_NatList_app_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.app Imported.Original_LF__DOT__Lists_LF_Lists_NatList_app Original_LF__DOT__Lists_LF_Lists_NatList_app_iso := {}.