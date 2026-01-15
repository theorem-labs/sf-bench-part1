From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__U_none__iso Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__cons__iso Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__nil__iso Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__nth____error__iso Isomorphisms.U_s__iso.

(* test_nth_error3 : nth_error [4;5;6;7] 9 = None - Admitted in Original.v *)
Monomorphic Definition imported_Original_LF__DOT__Lists_LF_Lists_NatList_test__nth__error3 := Imported.Original_LF__DOT__Lists_LF_Lists_NatList_test__nth__error3.

(* 4 = S S S S O, 5 = S 4, 6 = S 5, 7 = S 6, 9 = S S S S S S S S S O *)
Monomorphic Instance Original_LF__DOT__Lists_LF_Lists_NatList_test__nth__error3_iso : rel_iso
    (Corelib_Init_Logic_eq_iso
       (Original_LF__DOT__Lists_LF_Lists_NatList_nth__error_iso
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))
                (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))
                   (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))) Original_LF__DOT__Lists_LF_Lists_NatList_nil_iso))))
          (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))))))
       Original_LF__DOT__Lists_LF_Lists_NatList_None_iso)
    Original.LF_DOT_Lists.LF.Lists.NatList.test_nth_error3
    imported_Original_LF__DOT__Lists_LF_Lists_NatList_test__nth__error3.
Proof.
  (* test_nth_error3 is Admitted in Original.v, so we admit the isomorphism *)
  admit.
Admitted.
Instance: KnownConstant Original.LF_DOT_Lists.LF.Lists.NatList.test_nth_error3 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Lists_LF_Lists_NatList_test__nth__error3 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.test_nth_error3 Original_LF__DOT__Lists_LF_Lists_NatList_test__nth__error3_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.test_nth_error3 Imported.Original_LF__DOT__Lists_LF_Lists_NatList_test__nth__error3 Original_LF__DOT__Lists_LF_Lists_NatList_test__nth__error3_iso := {}.
