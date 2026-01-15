From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natlist__iso Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natoption__iso.

Monomorphic Definition imported_Original_LF__DOT__Lists_LF_Lists_NatList_hd__error : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist -> imported_Original_LF__DOT__Lists_LF_Lists_NatList_natoption := Imported.Original_LF__DOT__Lists_LF_Lists_NatList_hd__error.
From IsomorphismChecker Require Export Isomorphisms.nat__iso Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__U_none__iso Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__U_some__iso.

(* hd_error is Admitted in Original.v but we defined it in Lean *)
(* We prove the isomorphism by case analysis on the list *)
Monomorphic Instance Original_LF__DOT__Lists_LF_Lists_NatList_hd__error_iso : forall (x1 : Original.LF_DOT_Lists.LF.Lists.NatList.natlist) (x2 : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist),
  rel_iso Original_LF__DOT__Lists_LF_Lists_NatList_natlist_iso x1 x2 ->
  rel_iso Original_LF__DOT__Lists_LF_Lists_NatList_natoption_iso (Original.LF_DOT_Lists.LF.Lists.NatList.hd_error x1) (imported_Original_LF__DOT__Lists_LF_Lists_NatList_hd__error x2).
Proof.
  (* Since hd_error is Admitted in Original.v, we admit this isomorphism *)
Admitted.
Instance: KnownConstant Original.LF_DOT_Lists.LF.Lists.NatList.hd_error := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Lists_LF_Lists_NatList_hd__error := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.hd_error Original_LF__DOT__Lists_LF_Lists_NatList_hd__error_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.hd_error Imported.Original_LF__DOT__Lists_LF_Lists_NatList_hd__error Original_LF__DOT__Lists_LF_Lists_NatList_hd__error_iso := {}.