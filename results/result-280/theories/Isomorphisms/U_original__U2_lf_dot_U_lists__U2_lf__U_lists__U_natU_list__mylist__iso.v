From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natlist__iso.

Definition imported_Original_LF__DOT__Lists_LF_Lists_NatList_mylist : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist := Imported.Original_LF__DOT__Lists_LF_Lists_NatList_mylist.
Instance Original_LF__DOT__Lists_LF_Lists_NatList_mylist_iso : rel_iso Original_LF__DOT__Lists_LF_Lists_NatList_natlist_iso Original.LF_DOT_Lists.LF.Lists.NatList.mylist imported_Original_LF__DOT__Lists_LF_Lists_NatList_mylist.
Proof.
  unfold rel_iso. simpl.
  unfold imported_Original_LF__DOT__Lists_LF_Lists_NatList_mylist.
  unfold Imported.Original_LF__DOT__Lists_LF_Lists_NatList_mylist.
  unfold Imported.Original_LF__DOT__Lists_LF_Lists_NatList_cons.
  unfold Imported.Original_LF__DOT__Lists_LF_Lists_NatList_nil.
  unfold Original.LF_DOT_Lists.LF.Lists.NatList.mylist.
  simpl.
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_Lists.LF.Lists.NatList.mylist := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Lists_LF_Lists_NatList_mylist := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.mylist Original_LF__DOT__Lists_LF_Lists_NatList_mylist_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.mylist Imported.Original_LF__DOT__Lists_LF_Lists_NatList_mylist Original_LF__DOT__Lists_LF_Lists_NatList_mylist_iso := {}.