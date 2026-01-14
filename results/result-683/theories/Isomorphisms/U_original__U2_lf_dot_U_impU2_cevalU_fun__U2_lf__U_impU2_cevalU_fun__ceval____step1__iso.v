From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aeval__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__beval__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update__iso.

Definition imported_Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step1 : (imported_String_string -> imported_nat) -> imported_Original_LF__DOT__Imp_LF_Imp_com -> imported_String_string -> imported_nat := Imported.Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step1.

(* Reduction lemmas for the imported function *)
Lemma imported_ceval_step1_CSkip : forall st,
  Imported.Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step1 st Imported.Original_LF__DOT__Imp_LF_Imp_com_CSkip = st.
Proof. intros st. reflexivity. Qed.

Lemma imported_ceval_step1_CWhile : forall st b c,
  Imported.Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step1 st (Imported.Original_LF__DOT__Imp_LF_Imp_com_CWhile b c) = st.
Proof. intros st b c. reflexivity. Qed.

Lemma imported_ceval_step1_CAsgn : forall st x a,
  Imported.Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step1 st (Imported.Original_LF__DOT__Imp_LF_Imp_com_CAsgn x a) = 
  Imported.Original_LF__DOT__Maps_LF_Maps_t__update Imported.nat st x (Imported.Original_LF__DOT__Imp_LF_Imp_aeval st a).
Proof. intros st x a. reflexivity. Qed.

Lemma imported_ceval_step1_CSeq : forall st c1 c2,
  Imported.Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step1 st (Imported.Original_LF__DOT__Imp_LF_Imp_com_CSeq c1 c2) = 
  Imported.Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step1 
    (Imported.Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step1 st c1) c2.
Proof. intros st c1 c2. reflexivity. Qed.

Lemma imported_ceval_step1_CIf : forall st b c1 c2,
  Imported.Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step1 st (Imported.Original_LF__DOT__Imp_LF_Imp_com_CIf b c1 c2) = 
  match Imported.Original_LF__DOT__Imp_LF_Imp_beval st b with
  | Imported.mybool_mytrue => Imported.Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step1 st c1
  | Imported.mybool_myfalse => Imported.Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step1 st c2
  end.
Proof. intros. reflexivity. Qed.

(* Helper lemma to convert rel_iso for bool to equality *)
Lemma rel_iso_bool_to_eq : forall b1 b2,
  rel_iso bool_iso b1 b2 -> to bool_iso b1 = b2.
Proof.
  intros b1 b2 H.
  unfold rel_iso in H. simpl in H.
  apply eq_of_seq. exact H.
Qed.

(* Helper lemma to convert bool to mybool in beval *)
Lemma beval_to_mybool_iso : forall st1 st2 b,
  (forall x y, rel_iso String_string_iso x y -> rel_iso nat_iso (st1 x) (st2 y)) ->
  Original.LF_DOT_Imp.LF.Imp.beval st1 b = true ->
  Imported.Original_LF__DOT__Imp_LF_Imp_beval st2 (bexp_to_imported b) = Imported.mybool_mytrue.
Proof.
  intros st1 st2 b Hst Hbeval.
  pose proof (@Original_LF__DOT__Imp_LF_Imp_beval_iso st1 st2 Hst b (bexp_to_imported b) (@rel_iso_refl _ _ Original_LF__DOT__Imp_LF_Imp_bexp_iso b)) as H.
  apply rel_iso_bool_to_eq in H.
  simpl in H.
  rewrite Hbeval in H. simpl in H. symmetry. exact H.
Qed.

Lemma beval_to_mybool_iso_false : forall st1 st2 b,
  (forall x y, rel_iso String_string_iso x y -> rel_iso nat_iso (st1 x) (st2 y)) ->
  Original.LF_DOT_Imp.LF.Imp.beval st1 b = false ->
  Imported.Original_LF__DOT__Imp_LF_Imp_beval st2 (bexp_to_imported b) = Imported.mybool_myfalse.
Proof.
  intros st1 st2 b Hst Hbeval.
  pose proof (@Original_LF__DOT__Imp_LF_Imp_beval_iso st1 st2 Hst b (bexp_to_imported b) (@rel_iso_refl _ _ Original_LF__DOT__Imp_LF_Imp_bexp_iso b)) as H.
  apply rel_iso_bool_to_eq in H.
  simpl in H.
  rewrite Hbeval in H. simpl in H. symmetry. exact H.
Qed.

(* Helper to convert rel_iso for com to equality *)
Lemma rel_iso_com_to_eq : forall c1 c2,
  rel_iso Original_LF__DOT__Imp_LF_Imp_com_iso c1 c2 -> com_to_imported c1 = c2.
Proof.
  intros c1 c2 H.
  unfold rel_iso in H. simpl in H.
  apply eq_of_seq. exact H.
Qed.

(* Main theorem - use induction on command, with generalized state *)
Instance Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step1_iso : forall (x1 : Original.LF_DOT_Imp.LF.Imp.state) (x2 : imported_String_string -> imported_nat),
  (forall (x3 : String.string) (x4 : imported_String_string), rel_iso String_string_iso x3 x4 -> rel_iso nat_iso (x1 x3) (x2 x4)) ->
  forall (x3 : Original.LF_DOT_Imp.LF.Imp.com) (x4 : imported_Original_LF__DOT__Imp_LF_Imp_com),
  rel_iso Original_LF__DOT__Imp_LF_Imp_com_iso x3 x4 ->
  forall (x5 : String.string) (x6 : imported_String_string),
  rel_iso String_string_iso x5 x6 -> rel_iso nat_iso (Original.LF_DOT_ImpCEvalFun.LF.ImpCEvalFun.ceval_step1 x1 x3 x5) (imported_Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step1 x2 x4 x6).
Proof.
  (* Use a helper lemma with generalized states *)
  cut (forall c c', rel_iso Original_LF__DOT__Imp_LF_Imp_com_iso c c' ->
       forall st1 st2,
       (forall (x3 : String.string) (x4 : imported_String_string), rel_iso String_string_iso x3 x4 -> rel_iso nat_iso (st1 x3) (st2 x4)) ->
       forall s1 s2, rel_iso String_string_iso s1 s2 ->
       rel_iso nat_iso (Original.LF_DOT_ImpCEvalFun.LF.ImpCEvalFun.ceval_step1 st1 c s1) (imported_Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step1 st2 c' s2)).
  { intros H st1 st2 Hst c c' Hc s1 s2 Hs. exact (H c c' Hc st1 st2 Hst s1 s2 Hs). }
  fix IH 1. intros c.
  destruct c as [| x a | c1 c2 | b c1 c2 | b c1].
  all: intros c' Hc st1 st2 Hst s1 s2 Hs.
  all: apply rel_iso_com_to_eq in Hc; simpl in Hc; subst c'.
  - (* CSkip *)
    simpl. rewrite imported_ceval_step1_CSkip.
    apply Hst. exact Hs.
  - (* CAsgn *)
    simpl. rewrite imported_ceval_step1_CAsgn.
    set (hx := @RelaxIsoOrSort false _ _ (IsoIso nat_iso)).
    assert (HstSort : forall k1 k2, rel_iso String_string_iso k1 k2 -> rel_iso_sort hx (st1 k1) (st2 k2)).
    { intros k1 k2 Hk. specialize (Hst k1 k2 Hk). unfold rel_iso_sort, hx. simpl. unfold rel_iso in Hst. simpl in Hst. exact (wrap_sprop Hst). }
    assert (Haeval : rel_iso_sort hx (Original.LF_DOT_Imp.LF.Imp.aeval st1 a) (Imported.Original_LF__DOT__Imp_LF_Imp_aeval st2 (aexp_to_imported a))).
    { pose proof (@Original_LF__DOT__Imp_LF_Imp_aeval_iso st1 st2 Hst a (aexp_to_imported a) (@rel_iso_refl _ _ Original_LF__DOT__Imp_LF_Imp_aexp_iso a)) as Ha. unfold rel_iso_sort, hx. simpl. unfold rel_iso in Ha. simpl in Ha. exact (wrap_sprop Ha). }
    pose proof (@Original_LF__DOT__Maps_LF_Maps_t__update_iso nat imported_nat hx st1 st2 HstSort x (to String_string_iso x) (@rel_iso_refl _ _ String_string_iso x) _ _ Haeval s1 s2 Hs) as Hresult.
    unfold rel_iso_sort, hx in Hresult. simpl in Hresult. unfold rel_iso. simpl. exact (unwrap_sprop Hresult).
  - (* CSeq *)
    simpl. rewrite imported_ceval_step1_CSeq.
    set (st1' := Original.LF_DOT_ImpCEvalFun.LF.ImpCEvalFun.ceval_step1 st1 c1).
    set (st2' := Imported.Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step1 st2 (com_to_imported c1)).
    assert (Hst' : forall k1 k2, rel_iso String_string_iso k1 k2 -> rel_iso nat_iso (st1' k1) (st2' k2)).
    { intros k1 k2 Hk. unfold st1', st2'. apply (IH c1 (com_to_imported c1) (@rel_iso_refl _ _ Original_LF__DOT__Imp_LF_Imp_com_iso c1) st1 st2 Hst k1 k2 Hk). }
    apply (IH c2 (com_to_imported c2) (@rel_iso_refl _ _ Original_LF__DOT__Imp_LF_Imp_com_iso c2) st1' st2' Hst' s1 s2 Hs).
  - (* CIf *)
    simpl. rewrite imported_ceval_step1_CIf.
    destruct (Original.LF_DOT_Imp.LF.Imp.beval st1 b) eqn:Hbeval.
    + assert (Hbeval' : Imported.Original_LF__DOT__Imp_LF_Imp_beval st2 (bexp_to_imported b) = Imported.mybool_mytrue). { apply (beval_to_mybool_iso _ _ _ Hst Hbeval). }
      rewrite Hbeval'. exact (IH c1 (com_to_imported c1) (@rel_iso_refl _ _ Original_LF__DOT__Imp_LF_Imp_com_iso c1) st1 st2 Hst s1 s2 Hs).
    + assert (Hbeval' : Imported.Original_LF__DOT__Imp_LF_Imp_beval st2 (bexp_to_imported b) = Imported.mybool_myfalse). { apply (beval_to_mybool_iso_false _ _ _ Hst Hbeval). }
      rewrite Hbeval'. exact (IH c2 (com_to_imported c2) (@rel_iso_refl _ _ Original_LF__DOT__Imp_LF_Imp_com_iso c2) st1 st2 Hst s1 s2 Hs).
  - (* CWhile *)
    simpl. rewrite imported_ceval_step1_CWhile. apply Hst. exact Hs.
Qed.

Instance: KnownConstant Original.LF_DOT_ImpCEvalFun.LF.ImpCEvalFun.ceval_step1 := {}.
Instance: KnownConstant Imported.Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step1 := {}.
Instance: IsoStatementProofFor Original.LF_DOT_ImpCEvalFun.LF.ImpCEvalFun.ceval_step1 Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step1_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_ImpCEvalFun.LF.ImpCEvalFun.ceval_step1 Imported.Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step1 Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step1_iso := {}.
