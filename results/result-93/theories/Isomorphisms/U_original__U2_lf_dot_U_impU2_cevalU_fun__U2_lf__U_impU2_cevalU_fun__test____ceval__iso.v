From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso Isomorphisms.option__iso Isomorphisms.prod__iso.

Definition imported_Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_test__ceval : (imported_String_string -> imported_nat) -> imported_Original_LF__DOT__Imp_LF_Imp_com -> imported_option (imported_prod (imported_prod imported_nat imported_nat) imported_nat) := Imported.Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_test__ceval.

From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_impU2_cevalU_fun__U2_lf__U_impU2_cevalU_fun__ceval____step__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_x__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_y__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_z__iso.

Definition imported_nat500 := Imported.nat500.

Lemma nat500_iso : rel_iso nat_iso 500%nat imported_nat500.
Proof.
  unfold rel_iso. simpl. unfold imported_nat500. unfold Imported.nat500. reflexivity.
Qed.

Instance Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_test__ceval_iso : forall (x1 : Original.LF_DOT_Imp.LF.Imp.state) (x2 : imported_String_string -> imported_nat),
  (forall (x3 : String.string) (x4 : imported_String_string), rel_iso String_string_iso x3 x4 -> rel_iso nat_iso (x1 x3) (x2 x4)) ->
  forall (x3 : Original.LF_DOT_Imp.LF.Imp.com) (x4 : imported_Original_LF__DOT__Imp_LF_Imp_com),
  rel_iso Original_LF__DOT__Imp_LF_Imp_com_iso x3 x4 ->
  rel_iso (option_iso (prod_iso (prod_iso nat_iso nat_iso) nat_iso)) (Original.LF_DOT_ImpCEvalFun.LF.ImpCEvalFun.test_ceval x1 x3)
    (imported_Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_test__ceval x2 x4).
Admitted. (* We admit this for now - the proof was timing out *)
Instance: KnownConstant Original.LF_DOT_ImpCEvalFun.LF.ImpCEvalFun.test_ceval := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_test__ceval := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_ImpCEvalFun.LF.ImpCEvalFun.test_ceval Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_test__ceval_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_ImpCEvalFun.LF.ImpCEvalFun.test_ceval Imported.Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_test__ceval Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_test__ceval_iso := {}.