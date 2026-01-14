From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natlist__iso Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__Lists_LF_Lists_NatList_nth__bad : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist -> imported_nat -> imported_nat := Imported.Original_LF__DOT__Lists_LF_Lists_NatList_nth__bad.

(* Prove that the two nth_bad functions are equivalent under the isomorphisms *)
Lemma nth_bad_equiv : forall (l : Original.LF_DOT_Lists.LF.Lists.NatList.natlist) (n : nat),
  nat_to_imported (Original.LF_DOT_Lists.LF.Lists.NatList.nth_bad l n) = 
  Imported.Original_LF__DOT__Lists_LF_Lists_NatList_nth__bad (natlist_to_imported l) (nat_to_imported n).
Proof.
  fix IHl 1. intros l n. destruct l as [|h t].
  - (* nil case: returns 42 *)
    simpl. reflexivity.
  - (* cons case *)
    destruct n as [|n'].
    + (* n = 0: return the head *)
      simpl. reflexivity.
    + (* n = S n': recurse *)
      simpl. apply IHl.
Qed.

Instance Original_LF__DOT__Lists_LF_Lists_NatList_nth__bad_iso : forall (x1 : Original.LF_DOT_Lists.LF.Lists.NatList.natlist) (x2 : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist),
  rel_iso Original_LF__DOT__Lists_LF_Lists_NatList_natlist_iso x1 x2 ->
  forall (x3 : nat) (x4 : imported_nat),
  rel_iso nat_iso x3 x4 -> rel_iso nat_iso (Original.LF_DOT_Lists.LF.Lists.NatList.nth_bad x1 x3) (imported_Original_LF__DOT__Lists_LF_Lists_NatList_nth__bad x2 x4).
Proof.
  intros x1 x2 Hlist x3 x4 Hnat.
  unfold rel_iso in *.
  simpl in *.
  (* Hlist : natlist_to_imported x1 = x2 (SProp eq) *)
  (* Hnat : nat_to_imported x3 = x4 (SProp eq) *)
  (* Goal: nat_to_imported (nth_bad x1 x3) = nth_bad x2 x4 (SProp eq) *)
  (* We know: nat_to_imported (nth_bad x1 x3) = nth_bad (natlist_to_imported x1) (nat_to_imported x3) *)
  apply (eq_trans (seq_of_eq (nth_bad_equiv x1 x3))).
  apply (f_equal2 Imported.Original_LF__DOT__Lists_LF_Lists_NatList_nth__bad Hlist Hnat).
Qed.

Instance: KnownConstant Original.LF_DOT_Lists.LF.Lists.NatList.nth_bad := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Lists_LF_Lists_NatList_nth__bad := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.nth_bad Original_LF__DOT__Lists_LF_Lists_NatList_nth__bad_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.nth_bad Imported.Original_LF__DOT__Lists_LF_Lists_NatList_nth__bad Original_LF__DOT__Lists_LF_Lists_NatList_nth__bad_iso := {}.