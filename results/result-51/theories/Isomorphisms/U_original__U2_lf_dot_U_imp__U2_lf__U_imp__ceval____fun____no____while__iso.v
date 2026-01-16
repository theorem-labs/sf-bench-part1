From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
(* Typeclasses Opaque rel_iso. *) (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aeval__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__beval__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update__iso.

Definition imported_Original_LF__DOT__Imp_LF_Imp_ceval__fun__no__while : (imported_String_string -> imported_nat) -> imported_Original_LF__DOT__Imp_LF_Imp_com -> imported_String_string -> imported_nat := Imported.Original_LF__DOT__Imp_LF_Imp_ceval__fun__no__while.

(* Helper: state isomorphism relation *)
Definition state_rel (st : Original.LF_DOT_Imp.LF.Imp.state) (st' : imported_String_string -> imported_nat) : SProp :=
  forall (x : String.string) (x' : imported_String_string),
    rel_iso String_string_iso x x' -> rel_iso nat_iso (st x) (st' x').

(* Helper lemmas about how the imported ceval computes *)
Lemma imported_ceval_skip : forall st,
  Imported.Original_LF__DOT__Imp_LF_Imp_ceval__fun__no__while st Imported.Original_LF__DOT__Imp_LF_Imp_com_CSkip = st.
Proof. reflexivity. Qed.

Lemma imported_ceval_asgn : forall st y a,
  Imported.Original_LF__DOT__Imp_LF_Imp_ceval__fun__no__while st (Imported.Original_LF__DOT__Imp_LF_Imp_com_CAsgn y a)
  = Imported.Original_LF__DOT__Maps_LF_Maps_t__update imported_nat st y (Imported.Original_LF__DOT__Imp_LF_Imp_aeval st a).
Proof. reflexivity. Qed.

Lemma imported_ceval_seq : forall st c1 c2,
  Imported.Original_LF__DOT__Imp_LF_Imp_ceval__fun__no__while st (Imported.Original_LF__DOT__Imp_LF_Imp_com_CSeq c1 c2)
  = Imported.Original_LF__DOT__Imp_LF_Imp_ceval__fun__no__while 
      (Imported.Original_LF__DOT__Imp_LF_Imp_ceval__fun__no__while st c1) c2.
Proof. reflexivity. Qed.

Lemma imported_ceval_if : forall st b c1 c2,
  Imported.Original_LF__DOT__Imp_LF_Imp_ceval__fun__no__while st (Imported.Original_LF__DOT__Imp_LF_Imp_com_CIf b c1 c2)
  = match Imported.Original_LF__DOT__Imp_LF_Imp_beval st b with
    | Imported.mybool_mytrue => Imported.Original_LF__DOT__Imp_LF_Imp_ceval__fun__no__while st c1
    | Imported.mybool_myfalse => Imported.Original_LF__DOT__Imp_LF_Imp_ceval__fun__no__while st c2
    end.
Proof. reflexivity. Qed.

Lemma imported_ceval_while : forall st b c,
  Imported.Original_LF__DOT__Imp_LF_Imp_ceval__fun__no__while st (Imported.Original_LF__DOT__Imp_LF_Imp_com_CWhile b c) = st.
Proof. reflexivity. Qed.

Lemma ceval_iso_core : forall c (st : Original.LF_DOT_Imp.LF.Imp.state) (st' : imported_String_string -> imported_nat),
  state_rel st st' ->
  forall (x : String.string) (x' : imported_String_string),
  rel_iso String_string_iso x x' ->
  rel_iso nat_iso (Original.LF_DOT_Imp.LF.Imp.ceval_fun_no_while st c x)
            (imported_Original_LF__DOT__Imp_LF_Imp_ceval__fun__no__while st' (com_to_imported c) x').
Proof.
  fix IH 1.
  intros c st st' Hst x x' Hx.
  destruct c as [| y a | c1 c2 | b c1 c2 | b c1].
  - (* CSkip *)
    simpl. rewrite imported_ceval_skip.
    apply (Hst x x' Hx).
  - (* CAsgn y a *)
    simpl com_to_imported. unfold imported_Original_LF__DOT__Imp_LF_Imp_ceval__fun__no__while.
    rewrite imported_ceval_asgn.
    simpl Original.LF_DOT_Imp.LF.Imp.ceval_fun_no_while.
    unfold Original.LF_DOT_Maps.LF.Maps.t_update.
    unfold Imported.Original_LF__DOT__Maps_LF_Maps_t__update.
    pose proof (@string_eqb_compat y x (to String_string_iso y) x') as Heqb.
    pose proof (Heqb IsomorphismDefinitions.eq_refl Hx) as Heqb'.
    change (to String_string_iso y) with ((fix f (s : String.string) : imported_String_string :=
              match s with
              | String.EmptyString => Imported.String_string_EmptyString
              | String.String c rest => Imported.String_string_String (ascii_to c) (f rest)
              end) y) in Heqb'.
    destruct (String.eqb y x) eqn:E1.
    + (* y = x *)
      assert (E2 : Imported.String_eqb ((fix f (s : String.string) : imported_String_string :=
              match s with
              | String.EmptyString => Imported.String_string_EmptyString
              | String.String c rest => Imported.String_string_String (ascii_to c) (f rest)
              end) y) x' = Imported.mybool_mytrue).
      { apply eq_of_seq. apply (eq_trans (eq_sym Heqb')). simpl. exact IsomorphismDefinitions.eq_refl. }
      rewrite E2. simpl.
      constructor; simpl.
      apply (eq_trans (aeval_iso_core st st' Hst a)).
      apply (aeval_aux_eq st' (aexp_to_imported a)).
    + (* y <> x *)
      assert (E2 : Imported.String_eqb ((fix f (s : String.string) : imported_String_string :=
              match s with
              | String.EmptyString => Imported.String_string_EmptyString
              | String.String c rest => Imported.String_string_String (ascii_to c) (f rest)
              end) y) x' = Imported.mybool_myfalse).
      { apply eq_of_seq. apply (eq_trans (eq_sym Heqb')). simpl. exact IsomorphismDefinitions.eq_refl. }
      rewrite E2. simpl.
      apply (Hst x x' Hx).
  - (* CSeq c1 c2 *)
    simpl com_to_imported. unfold imported_Original_LF__DOT__Imp_LF_Imp_ceval__fun__no__while.
    rewrite imported_ceval_seq.
    simpl Original.LF_DOT_Imp.LF.Imp.ceval_fun_no_while.
    set (st1 := Original.LF_DOT_Imp.LF.Imp.ceval_fun_no_while st c1) in *.
    set (st1' := Imported.Original_LF__DOT__Imp_LF_Imp_ceval__fun__no__while st' (com_to_imported c1)) in *.
    assert (Hst1 : state_rel st1 st1').
    { unfold state_rel, st1, st1'. intros y y' Hy. apply (IH c1 st st' Hst y y' Hy). }
    apply (IH c2 st1 st1' Hst1 x x' Hx).
  - (* CIf b c1 c2 *)
    simpl com_to_imported. unfold imported_Original_LF__DOT__Imp_LF_Imp_ceval__fun__no__while.
    rewrite imported_ceval_if.
    simpl Original.LF_DOT_Imp.LF.Imp.ceval_fun_no_while.
    pose proof (beval_iso_core st st' Hst b) as Hbeval.
    pose proof (beval_aux_eq st' (bexp_to_imported b)) as Hbeval_eq.
    destruct (Original.LF_DOT_Imp.LF.Imp.beval st b) eqn:Eb.
    + (* beval st b = true *)
      assert (E2 : Imported.Original_LF__DOT__Imp_LF_Imp_beval st' (bexp_to_imported b) = Imported.mybool_mytrue).
      { apply eq_of_seq. apply (eq_trans (eq_sym Hbeval_eq)). 
        apply (eq_trans (eq_sym Hbeval)). simpl. exact IsomorphismDefinitions.eq_refl. }
      rewrite E2.
      apply (IH c1 st st' Hst x x' Hx).
    + (* beval st b = false *)
      assert (E2 : Imported.Original_LF__DOT__Imp_LF_Imp_beval st' (bexp_to_imported b) = Imported.mybool_myfalse).
      { apply eq_of_seq. apply (eq_trans (eq_sym Hbeval_eq)).
        apply (eq_trans (eq_sym Hbeval)). simpl. exact IsomorphismDefinitions.eq_refl. }
      rewrite E2.
      apply (IH c2 st st' Hst x x' Hx).
  - (* CWhile *)
    simpl. rewrite imported_ceval_while.
    apply (Hst x x' Hx).
Qed.

Instance Original_LF__DOT__Imp_LF_Imp_ceval__fun__no__while_iso : forall (x1 : Original.LF_DOT_Imp.LF.Imp.state) (x2 : imported_String_string -> imported_nat),
  (forall (x3 : String.string) (x4 : imported_String_string), rel_iso String_string_iso x3 x4 -> rel_iso nat_iso (x1 x3) (x2 x4)) ->
  forall (x3 : Original.LF_DOT_Imp.LF.Imp.com) (x4 : imported_Original_LF__DOT__Imp_LF_Imp_com),
  rel_iso Original_LF__DOT__Imp_LF_Imp_com_iso x3 x4 ->
  forall (x5 : String.string) (x6 : imported_String_string),
  rel_iso String_string_iso x5 x6 -> rel_iso nat_iso (Original.LF_DOT_Imp.LF.Imp.ceval_fun_no_while x1 x3 x5) (imported_Original_LF__DOT__Imp_LF_Imp_ceval__fun__no__while x2 x4 x6).
Proof.
  intros st st' Hst c c' Hc x x' Hx.
  pose proof (proj_rel_iso Hc) as Hc_eq; simpl in Hc_eq.
  assert (Hst' : state_rel st st') by exact Hst.
  pose proof (@ceval_iso_core c st st' Hst' x x' Hx) as H1.
  pose proof (proj_rel_iso H1) as H1_eq; simpl in H1_eq.
  constructor; simpl.
  apply (eq_trans H1_eq).
  apply (f_equal (fun f => f x')).
  apply (f_equal (imported_Original_LF__DOT__Imp_LF_Imp_ceval__fun__no__while st') Hc_eq).
Defined.
Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.ceval_fun_no_while := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_ceval__fun__no__while := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.ceval_fun_no_while Original_LF__DOT__Imp_LF_Imp_ceval__fun__no__while_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.ceval_fun_no_while Imported.Original_LF__DOT__Imp_LF_Imp_ceval__fun__no__while Original_LF__DOT__Imp_LF_Imp_ceval__fun__no__while_iso := {}.