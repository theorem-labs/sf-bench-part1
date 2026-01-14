From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__app__iso Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__cons__iso Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__nil__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__Lists_LF_Lists_NatList_test__app2 : imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__Lists_LF_Lists_NatList_app imported_Original_LF__DOT__Lists_LF_Lists_NatList_nil
       (imported_Original_LF__DOT__Lists_LF_Lists_NatList_cons (imported_S (imported_S (imported_S (imported_S imported_0))))
          (imported_Original_LF__DOT__Lists_LF_Lists_NatList_cons (imported_S (imported_S (imported_S (imported_S (imported_S imported_0))))) imported_Original_LF__DOT__Lists_LF_Lists_NatList_nil)))
    (imported_Original_LF__DOT__Lists_LF_Lists_NatList_cons (imported_S (imported_S (imported_S (imported_S imported_0))))
       (imported_Original_LF__DOT__Lists_LF_Lists_NatList_cons (imported_S (imported_S (imported_S (imported_S (imported_S imported_0))))) imported_Original_LF__DOT__Lists_LF_Lists_NatList_nil)) := Imported.Original_LF__DOT__Lists_LF_Lists_NatList_test__app2.
Instance Original_LF__DOT__Lists_LF_Lists_NatList_test__app2_iso : rel_iso
    {|
      to :=
        Corelib_Init_Logic_eq_iso
          (Original_LF__DOT__Lists_LF_Lists_NatList_app_iso Original_LF__DOT__Lists_LF_Lists_NatList_nil_iso
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))
                (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))) Original_LF__DOT__Lists_LF_Lists_NatList_nil_iso)))
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))) Original_LF__DOT__Lists_LF_Lists_NatList_nil_iso));
      from :=
        from
          (Corelib_Init_Logic_eq_iso
             (Original_LF__DOT__Lists_LF_Lists_NatList_app_iso Original_LF__DOT__Lists_LF_Lists_NatList_nil_iso
                (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))
                   (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))) Original_LF__DOT__Lists_LF_Lists_NatList_nil_iso)))
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))
                (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))) Original_LF__DOT__Lists_LF_Lists_NatList_nil_iso)));
      to_from :=
        fun
          x : imported_Corelib_Init_Logic_eq
                (imported_Original_LF__DOT__Lists_LF_Lists_NatList_app imported_Original_LF__DOT__Lists_LF_Lists_NatList_nil
                   (imported_Original_LF__DOT__Lists_LF_Lists_NatList_cons (imported_S (imported_S (imported_S (imported_S imported_0))))
                      (imported_Original_LF__DOT__Lists_LF_Lists_NatList_cons (imported_S (imported_S (imported_S (imported_S (imported_S imported_0)))))
                         imported_Original_LF__DOT__Lists_LF_Lists_NatList_nil)))
                (imported_Original_LF__DOT__Lists_LF_Lists_NatList_cons (imported_S (imported_S (imported_S (imported_S imported_0))))
                   (imported_Original_LF__DOT__Lists_LF_Lists_NatList_cons (imported_S (imported_S (imported_S (imported_S (imported_S imported_0)))))
                      imported_Original_LF__DOT__Lists_LF_Lists_NatList_nil)) =>
        to_from
          (Corelib_Init_Logic_eq_iso
             (Original_LF__DOT__Lists_LF_Lists_NatList_app_iso Original_LF__DOT__Lists_LF_Lists_NatList_nil_iso
                (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))
                   (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))) Original_LF__DOT__Lists_LF_Lists_NatList_nil_iso)))
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))
                (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))) Original_LF__DOT__Lists_LF_Lists_NatList_nil_iso)))
          x;
      from_to :=
        fun
          x : Original.LF_DOT_Lists.LF.Lists.NatList.app Original.LF_DOT_Lists.LF.Lists.NatList.nil
                (Original.LF_DOT_Lists.LF.Lists.NatList.cons 4 (Original.LF_DOT_Lists.LF.Lists.NatList.cons 5 Original.LF_DOT_Lists.LF.Lists.NatList.nil)) =
              Original.LF_DOT_Lists.LF.Lists.NatList.cons 4 (Original.LF_DOT_Lists.LF.Lists.NatList.cons 5 Original.LF_DOT_Lists.LF.Lists.NatList.nil) =>
        seq_p_of_t
          (from_to
             (Corelib_Init_Logic_eq_iso
                (Original_LF__DOT__Lists_LF_Lists_NatList_app_iso Original_LF__DOT__Lists_LF_Lists_NatList_nil_iso
                   (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))
                      (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))) Original_LF__DOT__Lists_LF_Lists_NatList_nil_iso)))
                (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))
                   (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))) Original_LF__DOT__Lists_LF_Lists_NatList_nil_iso)))
             x)
    |} Original.LF_DOT_Lists.LF.Lists.NatList.test_app2 imported_Original_LF__DOT__Lists_LF_Lists_NatList_test__app2.
Proof.
  (* The original test_app2 is an Admitted axiom: nil ++ [4;5] = [4;5] 
     The imported version is also an axiom.
     We need to show that the isomorphism maps one to the other.
     Since both are proofs of equality (which is in SProp for imported), 
     we can use the fact that the isomorphism's to function applied to
     the original axiom gives a proof of the imported equality. *)
  unfold rel_iso.
  simpl.
  (* The goal is now an equality in SProp, which is proof-irrelevant *)
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_Lists.LF.Lists.NatList.test_app2 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Lists_LF_Lists_NatList_test__app2 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.test_app2 Original_LF__DOT__Lists_LF_Lists_NatList_test__app2_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.test_app2 Imported.Original_LF__DOT__Lists_LF_Lists_NatList_test__app2 Original_LF__DOT__Lists_LF_Lists_NatList_test__app2_iso := {}.