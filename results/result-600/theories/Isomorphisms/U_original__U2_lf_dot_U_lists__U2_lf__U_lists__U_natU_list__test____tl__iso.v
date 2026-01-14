From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__cons__iso Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__nil__iso Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__tl__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__Lists_LF_Lists_NatList_test__tl : imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__Lists_LF_Lists_NatList_tl
       (imported_Original_LF__DOT__Lists_LF_Lists_NatList_cons (imported_S imported_0)
          (imported_Original_LF__DOT__Lists_LF_Lists_NatList_cons (imported_S (imported_S imported_0))
             (imported_Original_LF__DOT__Lists_LF_Lists_NatList_cons (imported_S (imported_S (imported_S imported_0))) imported_Original_LF__DOT__Lists_LF_Lists_NatList_nil))))
    (imported_Original_LF__DOT__Lists_LF_Lists_NatList_cons (imported_S (imported_S imported_0))
       (imported_Original_LF__DOT__Lists_LF_Lists_NatList_cons (imported_S (imported_S (imported_S imported_0))) imported_Original_LF__DOT__Lists_LF_Lists_NatList_nil)) := Imported.Original_LF__DOT__Lists_LF_Lists_NatList_test__tl.
Instance Original_LF__DOT__Lists_LF_Lists_NatList_test__tl_iso : rel_iso
    (relax_Iso_Ts_Ps
       (Corelib_Init_Logic_eq_iso
          (Original_LF__DOT__Lists_LF_Lists_NatList_tl_iso
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso _0_iso)
                (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso _0_iso))
                   (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso _0_iso))) Original_LF__DOT__Lists_LF_Lists_NatList_nil_iso))))
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso _0_iso))
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso _0_iso))) Original_LF__DOT__Lists_LF_Lists_NatList_nil_iso))))
    Original.LF_DOT_Lists.LF.Lists.NatList.test_tl imported_Original_LF__DOT__Lists_LF_Lists_NatList_test__tl.
Proof.
  unfold rel_iso. simpl.
  (* The goal is an SProp equality - both sides are proofs in SProp, so they are equal *)
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_Lists.LF.Lists.NatList.test_tl := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Lists_LF_Lists_NatList_test__tl := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.test_tl Original_LF__DOT__Lists_LF_Lists_NatList_test__tl_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.test_tl Imported.Original_LF__DOT__Lists_LF_Lists_NatList_test__tl Original_LF__DOT__Lists_LF_Lists_NatList_test__tl_iso := {}.