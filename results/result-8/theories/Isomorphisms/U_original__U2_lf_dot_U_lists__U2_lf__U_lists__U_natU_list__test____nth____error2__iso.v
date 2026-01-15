From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__U_some__iso Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__cons__iso Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__nil__iso Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__nth____error__iso Isomorphisms.U_s__iso.

(* test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7 - Admitted in Original.v *)
Monomorphic Definition imported_Original_LF__DOT__Lists_LF_Lists_NatList_test__nth__error2 := Imported.Original_LF__DOT__Lists_LF_Lists_NatList_test__nth__error2.

Monomorphic Instance Original_LF__DOT__Lists_LF_Lists_NatList_test__nth__error2_iso : rel_iso
    (Corelib_Init_Logic_eq_iso
       (Original_LF__DOT__Lists_LF_Lists_NatList_nth__error_iso
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))
                (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))
                   (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))) Original_LF__DOT__Lists_LF_Lists_NatList_nil_iso))))
          (S_iso (S_iso (S_iso _0_iso))))
       (Original_LF__DOT__Lists_LF_Lists_NatList_Some_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))))))
    Original.LF_DOT_Lists.LF.Lists.NatList.test_nth_error2
    imported_Original_LF__DOT__Lists_LF_Lists_NatList_test__nth__error2.
Proof.
  (* test_nth_error2 is Admitted in Original.v, so we admit the isomorphism *)
  admit.
Admitted.
Instance: KnownConstant Original.LF_DOT_Lists.LF.Lists.NatList.test_nth_error2 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Lists_LF_Lists_NatList_test__nth__error2 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.test_nth_error2 Original_LF__DOT__Lists_LF_Lists_NatList_test__nth__error2_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.test_nth_error2 Imported.Original_LF__DOT__Lists_LF_Lists_NatList_test__nth__error2 Original_LF__DOT__Lists_LF_Lists_NatList_test__nth__error2_iso := {}.
