From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__U_some__iso Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__cons__iso Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__nil__iso Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__nth____error__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__Lists_LF_Lists_NatList_test__nth__error1 : imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__Lists_LF_Lists_NatList_nth__error
       (imported_Original_LF__DOT__Lists_LF_Lists_NatList_cons (imported_S (imported_S (imported_S (imported_S imported_0))))
          (imported_Original_LF__DOT__Lists_LF_Lists_NatList_cons (imported_S (imported_S (imported_S (imported_S (imported_S imported_0)))))
             (imported_Original_LF__DOT__Lists_LF_Lists_NatList_cons (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S imported_0))))))
                (imported_Original_LF__DOT__Lists_LF_Lists_NatList_cons (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S imported_0)))))))
                   imported_Original_LF__DOT__Lists_LF_Lists_NatList_nil))))
       imported_0)
    (imported_Original_LF__DOT__Lists_LF_Lists_NatList_Some (imported_S (imported_S (imported_S (imported_S imported_0))))) := Imported.Original_LF__DOT__Lists_LF_Lists_NatList_test__nth__error1.
Instance Original_LF__DOT__Lists_LF_Lists_NatList_test__nth__error1_iso : rel_iso
    {|
      to :=
        Corelib_Init_Logic_eq_iso
          (Original_LF__DOT__Lists_LF_Lists_NatList_nth__error_iso
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))
                (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))
                   (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))
                      (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))) Original_LF__DOT__Lists_LF_Lists_NatList_nil_iso))))
             _0_iso)
          (Original_LF__DOT__Lists_LF_Lists_NatList_Some_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))));
      from :=
        from
          (Corelib_Init_Logic_eq_iso
             (Original_LF__DOT__Lists_LF_Lists_NatList_nth__error_iso
                (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))
                   (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))
                      (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))
                         (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))) Original_LF__DOT__Lists_LF_Lists_NatList_nil_iso))))
                _0_iso)
             (Original_LF__DOT__Lists_LF_Lists_NatList_Some_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))));
      to_from :=
        fun
          x : imported_Corelib_Init_Logic_eq
                (imported_Original_LF__DOT__Lists_LF_Lists_NatList_nth__error
                   (imported_Original_LF__DOT__Lists_LF_Lists_NatList_cons (imported_S (imported_S (imported_S (imported_S imported_0))))
                      (imported_Original_LF__DOT__Lists_LF_Lists_NatList_cons (imported_S (imported_S (imported_S (imported_S (imported_S imported_0)))))
                         (imported_Original_LF__DOT__Lists_LF_Lists_NatList_cons (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S imported_0))))))
                            (imported_Original_LF__DOT__Lists_LF_Lists_NatList_cons (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S imported_0)))))))
                               imported_Original_LF__DOT__Lists_LF_Lists_NatList_nil))))
                   imported_0)
                (imported_Original_LF__DOT__Lists_LF_Lists_NatList_Some (imported_S (imported_S (imported_S (imported_S imported_0))))) =>
        to_from
          (Corelib_Init_Logic_eq_iso
             (Original_LF__DOT__Lists_LF_Lists_NatList_nth__error_iso
                (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))
                   (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))
                      (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))
                         (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))) Original_LF__DOT__Lists_LF_Lists_NatList_nil_iso))))
                _0_iso)
             (Original_LF__DOT__Lists_LF_Lists_NatList_Some_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))
          x;
      from_to :=
        fun
          x : Original.LF_DOT_Lists.LF.Lists.NatList.nth_error
                (Original.LF_DOT_Lists.LF.Lists.NatList.cons 4
                   (Original.LF_DOT_Lists.LF.Lists.NatList.cons 5
                      (Original.LF_DOT_Lists.LF.Lists.NatList.cons 6 (Original.LF_DOT_Lists.LF.Lists.NatList.cons 7 Original.LF_DOT_Lists.LF.Lists.NatList.nil))))
                0 =
              Original.LF_DOT_Lists.LF.Lists.NatList.Some 4 =>
        seq_p_of_t
          (from_to
             (Corelib_Init_Logic_eq_iso
                (Original_LF__DOT__Lists_LF_Lists_NatList_nth__error_iso
                   (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))
                      (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))
                         (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))
                            (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))) Original_LF__DOT__Lists_LF_Lists_NatList_nil_iso))))
                   _0_iso)
                (Original_LF__DOT__Lists_LF_Lists_NatList_Some_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))
             x)
    |} Original.LF_DOT_Lists.LF.Lists.NatList.test_nth_error1 imported_Original_LF__DOT__Lists_LF_Lists_NatList_test__nth__error1.
Proof.
  unfold rel_iso. simpl.
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_Lists.LF.Lists.NatList.test_nth_error1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Lists_LF_Lists_NatList_test__nth__error1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.test_nth_error1 Original_LF__DOT__Lists_LF_Lists_NatList_test__nth__error1_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.test_nth_error1 Imported.Original_LF__DOT__Lists_LF_Lists_NatList_test__nth__error1 Original_LF__DOT__Lists_LF_Lists_NatList_test__nth__error1_iso := {}.