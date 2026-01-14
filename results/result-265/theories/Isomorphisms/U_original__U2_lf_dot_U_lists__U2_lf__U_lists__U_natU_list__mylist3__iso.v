From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natlist__iso.

Definition imported_Original_LF__DOT__Lists_LF_Lists_NatList_mylist3 : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist := Imported.Original_LF__DOT__Lists_LF_Lists_NatList_mylist3.

Instance Original_LF__DOT__Lists_LF_Lists_NatList_mylist3_iso : rel_iso Original_LF__DOT__Lists_LF_Lists_NatList_natlist_iso Original.LF_DOT_Lists.LF.Lists.NatList.mylist3 imported_Original_LF__DOT__Lists_LF_Lists_NatList_mylist3.
Proof.
  unfold rel_iso, imported_Original_LF__DOT__Lists_LF_Lists_NatList_mylist3.
  simpl.
  (* mylist3 = [1;2;3] = cons 1 (cons 2 (cons 3 nil)) *)
  (* We need to show that natlist_to_imported applied to the original equals the imported *)
  apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_Lists.LF.Lists.NatList.mylist3 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Lists_LF_Lists_NatList_mylist3 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.mylist3 Original_LF__DOT__Lists_LF_Lists_NatList_mylist3_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.mylist3 Imported.Original_LF__DOT__Lists_LF_Lists_NatList_mylist3 Original_LF__DOT__Lists_LF_Lists_NatList_mylist3_iso := {}.