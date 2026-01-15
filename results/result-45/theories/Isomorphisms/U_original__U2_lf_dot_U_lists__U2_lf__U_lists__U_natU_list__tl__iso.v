From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natlist__iso.

Monomorphic Definition imported_Original_LF__DOT__Lists_LF_Lists_NatList_tl : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist -> imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist := Imported.Original_LF__DOT__Lists_LF_Lists_NatList_tl.

(* Prove tl commutes *)
Lemma tl_commutes : forall (l : Original.LF_DOT_Lists.LF.Lists.NatList.natlist),
  Logic.eq (natlist_to_imported (Original.LF_DOT_Lists.LF.Lists.NatList.tl l))
           (Imported.Original_LF__DOT__Lists_LF_Lists_NatList_tl (natlist_to_imported l)).
Proof.
  intro l. destruct l; reflexivity.
Defined.

Monomorphic Instance Original_LF__DOT__Lists_LF_Lists_NatList_tl_iso : forall (x1 : Original.LF_DOT_Lists.LF.Lists.NatList.natlist) (x2 : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist),
  rel_iso Original_LF__DOT__Lists_LF_Lists_NatList_natlist_iso x1 x2 ->
  rel_iso Original_LF__DOT__Lists_LF_Lists_NatList_natlist_iso (Original.LF_DOT_Lists.LF.Lists.NatList.tl x1) (imported_Original_LF__DOT__Lists_LF_Lists_NatList_tl x2).
Proof.
  intros x1 x2 H1.
  destruct H1 as [H1']. constructor. simpl.
  unfold imported_Original_LF__DOT__Lists_LF_Lists_NatList_tl.
  pose proof (seq_of_eq (tl_commutes x1)) as Hcomm.
  pose proof (f_equal Imported.Original_LF__DOT__Lists_LF_Lists_NatList_tl H1') as Harg.
  apply (eq_trans Hcomm Harg).
Defined.
Instance: KnownConstant Original.LF_DOT_Lists.LF.Lists.NatList.tl := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Lists_LF_Lists_NatList_tl := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.tl Original_LF__DOT__Lists_LF_Lists_NatList_tl_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.tl Imported.Original_LF__DOT__Lists_LF_Lists_NatList_tl Original_LF__DOT__Lists_LF_Lists_NatList_tl_iso := {}.