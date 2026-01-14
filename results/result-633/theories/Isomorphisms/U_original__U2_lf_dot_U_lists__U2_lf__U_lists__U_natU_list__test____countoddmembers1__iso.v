From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__cons__iso Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__countoddmembers__iso Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__nil__iso Isomorphisms.U_s__iso.

(* The list [1;0;3;1;4;5] in imported form and result 4 *)
(* 4 = S(S(S(S(0)))) and 5 = S(S(S(S(S(0))))) *)
Definition imported_4 : imported_nat := imported_S (imported_S (imported_S (imported_S imported_0))).
Definition imported_5 : imported_nat := imported_S (imported_S (imported_S (imported_S (imported_S imported_0)))).

Definition imported_Original_LF__DOT__Lists_LF_Lists_NatList_test__countoddmembers1 : imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__Lists_LF_Lists_NatList_countoddmembers
       (imported_Original_LF__DOT__Lists_LF_Lists_NatList_cons (imported_S imported_0)  (* 1 *)
          (imported_Original_LF__DOT__Lists_LF_Lists_NatList_cons imported_0  (* 0 *)
             (imported_Original_LF__DOT__Lists_LF_Lists_NatList_cons (imported_S (imported_S (imported_S imported_0)))  (* 3 *)
                (imported_Original_LF__DOT__Lists_LF_Lists_NatList_cons (imported_S imported_0)  (* 1 *)
                   (imported_Original_LF__DOT__Lists_LF_Lists_NatList_cons imported_4  (* 4 *)
                      (imported_Original_LF__DOT__Lists_LF_Lists_NatList_cons imported_5  (* 5 *)
                         imported_Original_LF__DOT__Lists_LF_Lists_NatList_nil)))))))
    imported_4  (* result = 4 *)
    := Imported.Original_LF__DOT__Lists_LF_Lists_NatList_test__countoddmembers1.

(* Isomorphism proofs for 4 and 5 *)
Definition original_4 : nat := S (S (S (S O))).
Definition original_5 : nat := S (S (S (S (S O)))).
Definition _4_iso : rel_iso nat_iso original_4 imported_4 := S_iso (S_iso (S_iso (S_iso _0_iso))).
Definition _5_iso : rel_iso nat_iso original_5 imported_5 := S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))).

Instance Original_LF__DOT__Lists_LF_Lists_NatList_test__countoddmembers1_iso : rel_iso
    (relax_Iso_Ts_Ps
       (Corelib_Init_Logic_eq_iso
          (Original_LF__DOT__Lists_LF_Lists_NatList_countoddmembers_iso
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso _0_iso)  (* 1 *)
                (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso _0_iso  (* 0 *)
                   (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso _0_iso)))  (* 3 *)
                      (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso _0_iso)  (* 1 *)
                         (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso _4_iso  (* 4 *)
                            (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso _5_iso  (* 5 *)
                               Original_LF__DOT__Lists_LF_Lists_NatList_nil_iso)))))))
          _4_iso))  (* result = 4 *)
    Original.LF_DOT_Lists.LF.Lists.NatList.test_countoddmembers1 imported_Original_LF__DOT__Lists_LF_Lists_NatList_test__countoddmembers1.
Admitted.
Instance: KnownConstant Original.LF_DOT_Lists.LF.Lists.NatList.test_countoddmembers1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Lists_LF_Lists_NatList_test__countoddmembers1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.test_countoddmembers1 Original_LF__DOT__Lists_LF_Lists_NatList_test__countoddmembers1_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.test_countoddmembers1 Imported.Original_LF__DOT__Lists_LF_Lists_NatList_test__countoddmembers1 Original_LF__DOT__Lists_LF_Lists_NatList_test__countoddmembers1_iso := {}.