From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natlist__iso Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natoption__iso Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__Lists_LF_Lists_NatList_nth__error : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist -> imported_nat -> imported_Original_LF__DOT__Lists_LF_Lists_NatList_natoption := Imported.Original_LF__DOT__Lists_LF_Lists_NatList_nth__error.

(* Helper lemma: nth_error preserves isomorphism *)
Lemma nth_error_preserves_iso : forall (l : Original.LF_DOT_Lists.LF.Lists.NatList.natlist) (n : nat),
  Logic.eq (natoption_to_imported (Original.LF_DOT_Lists.LF.Lists.NatList.nth_error l n))
           (Imported.Original_LF__DOT__Lists_LF_Lists_NatList_nth__error (natlist_to_imported l) (nat_to_imported n)).
Proof.
  fix IHl 1.
  intros l n.
  destruct l as [| a l']; simpl.
  - (* nil case *)
    reflexivity.
  - (* cons case *)
    destruct n as [| n']; simpl.
    + (* n = 0 *)
      reflexivity.
    + (* n = S n' *)
      apply IHl.
Qed.

Instance Original_LF__DOT__Lists_LF_Lists_NatList_nth__error_iso : forall (x1 : Original.LF_DOT_Lists.LF.Lists.NatList.natlist) (x2 : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist),
  rel_iso Original_LF__DOT__Lists_LF_Lists_NatList_natlist_iso x1 x2 ->
  forall (x3 : nat) (x4 : imported_nat),
  rel_iso nat_iso x3 x4 ->
  rel_iso Original_LF__DOT__Lists_LF_Lists_NatList_natoption_iso (Original.LF_DOT_Lists.LF.Lists.NatList.nth_error x1 x3) (imported_Original_LF__DOT__Lists_LF_Lists_NatList_nth__error x2 x4).
Proof.
  intros x1 x2 Hlist x3 x4 Hnat.
  unfold rel_iso in Hlist, Hnat |- *. simpl in Hlist, Hnat |- *.
  unfold imported_Original_LF__DOT__Lists_LF_Lists_NatList_nth__error.
  (* Use eq_of_seq to get a Logic.eq from the SProp eq *)
  pose proof (eq_of_seq Hlist) as Hlist'.
  pose proof (eq_of_seq Hnat) as Hnat'.
  rewrite <- Hlist', <- Hnat'.
  apply seq_of_eq.
  apply nth_error_preserves_iso.
Defined.

Instance: KnownConstant Original.LF_DOT_Lists.LF.Lists.NatList.nth_error := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Lists_LF_Lists_NatList_nth__error := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.nth_error Original_LF__DOT__Lists_LF_Lists_NatList_nth__error_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.nth_error Imported.Original_LF__DOT__Lists_LF_Lists_NatList_nth__error Original_LF__DOT__Lists_LF_Lists_NatList_nth__error_iso := {}.