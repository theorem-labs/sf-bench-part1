From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_re__chars : forall x : Type, imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp x -> imported_Original_LF__DOT__Poly_LF_Poly_list x := (@Imported.Original_LF__DOT__IndProp_LF_IndProp_re__chars).

(* Helper lemma: re_chars preserves the isomorphism *)
Lemma re_chars_iso_helper : forall (x1 x2 : Type) (hx : Iso x1 x2)
  (re : Original.LF_DOT_IndProp.LF.IndProp.reg_exp x1),
  IsomorphismDefinitions.eq
    (to (Original_LF__DOT__Poly_LF_Poly_list_iso hx) (Original.LF_DOT_IndProp.LF.IndProp.re_chars re))
    (Imported.Original_LF__DOT__IndProp_LF_IndProp_re__chars x2 
      (to (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) re)).
Proof.
  intros x1 x2 hx re.
  induction re as [| | t | r1 IH1 r2 IH2 | r1 IH1 r2 IH2 | r IH].
  all: try (apply IsomorphismDefinitions.eq_refl).
  - (* App r1 r2 *)
    simpl Original.LF_DOT_IndProp.LF.IndProp.re_chars.
    simpl to at 1.
    change (to (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) (Original.LF_DOT_IndProp.LF.IndProp.App r1 r2))
      with (Imported.Original_LF__DOT__IndProp_LF_IndProp_reg__exp_App x2
              (to (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) r1)
              (to (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) r2)).
    change (Imported.Original_LF__DOT__IndProp_LF_IndProp_re__chars x2
              (Imported.Original_LF__DOT__IndProp_LF_IndProp_reg__exp_App x2
                 (to (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) r1)
                 (to (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) r2)))
      with (Imported.Original_LF__DOT__Poly_LF_Poly_app x2
              (Imported.Original_LF__DOT__IndProp_LF_IndProp_re__chars x2 (to (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) r1))
              (Imported.Original_LF__DOT__IndProp_LF_IndProp_re__chars x2 (to (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) r2))).
    apply (@IsoEq.eq_trans _ _
             (Imported.Original_LF__DOT__Poly_LF_Poly_app x2
                (to (Original_LF__DOT__Poly_LF_Poly_list_iso hx) (Original.LF_DOT_IndProp.LF.IndProp.re_chars r1))
                (to (Original_LF__DOT__Poly_LF_Poly_list_iso hx) (Original.LF_DOT_IndProp.LF.IndProp.re_chars r2))) _).
    { apply list_to_app_compat. }
    { apply IsoEq.f_equal2; assumption. }
  - (* Union r1 r2 *)
    simpl Original.LF_DOT_IndProp.LF.IndProp.re_chars.
    simpl to at 1.
    change (to (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) (Original.LF_DOT_IndProp.LF.IndProp.Union r1 r2))
      with (Imported.Original_LF__DOT__IndProp_LF_IndProp_reg__exp_Union x2
              (to (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) r1)
              (to (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) r2)).
    change (Imported.Original_LF__DOT__IndProp_LF_IndProp_re__chars x2
              (Imported.Original_LF__DOT__IndProp_LF_IndProp_reg__exp_Union x2
                 (to (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) r1)
                 (to (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) r2)))
      with (Imported.Original_LF__DOT__Poly_LF_Poly_app x2
              (Imported.Original_LF__DOT__IndProp_LF_IndProp_re__chars x2 (to (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) r1))
              (Imported.Original_LF__DOT__IndProp_LF_IndProp_re__chars x2 (to (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) r2))).
    apply (@IsoEq.eq_trans _ _
             (Imported.Original_LF__DOT__Poly_LF_Poly_app x2
                (to (Original_LF__DOT__Poly_LF_Poly_list_iso hx) (Original.LF_DOT_IndProp.LF.IndProp.re_chars r1))
                (to (Original_LF__DOT__Poly_LF_Poly_list_iso hx) (Original.LF_DOT_IndProp.LF.IndProp.re_chars r2))) _).
    { apply list_to_app_compat. }
    { apply IsoEq.f_equal2; assumption. }
  - (* Star r *)
    simpl Original.LF_DOT_IndProp.LF.IndProp.re_chars.
    simpl to at 1.
    change (to (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) (Original.LF_DOT_IndProp.LF.IndProp.Star r))
      with (Imported.Original_LF__DOT__IndProp_LF_IndProp_reg__exp_Star x2
              (to (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) r)).
    change (Imported.Original_LF__DOT__IndProp_LF_IndProp_re__chars x2
              (Imported.Original_LF__DOT__IndProp_LF_IndProp_reg__exp_Star x2
                 (to (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) r)))
      with (Imported.Original_LF__DOT__IndProp_LF_IndProp_re__chars x2 (to (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) r)).
    exact IH.
Defined.

Instance Original_LF__DOT__IndProp_LF_IndProp_re__chars_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_IndProp.LF.IndProp.reg_exp x1) (x4 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp x2),
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) x3 x4 ->
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) (Original.LF_DOT_IndProp.LF.IndProp.re_chars x3) (imported_Original_LF__DOT__IndProp_LF_IndProp_re__chars x4).
Proof.
  intros x1 x2 hx x3 x4 Hx34.
  unfold rel_iso in *.
  unfold imported_Original_LF__DOT__IndProp_LF_IndProp_re__chars.
  apply (@IsoEq.eq_trans _ _
           (Imported.Original_LF__DOT__IndProp_LF_IndProp_re__chars x2
              (to (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) x3)) _).
  - apply re_chars_iso_helper.
  - apply IsoEq.f_equal. exact Hx34.
Defined.
Instance: KnownConstant (@Original.LF_DOT_IndProp.LF.IndProp.re_chars) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Original_LF__DOT__IndProp_LF_IndProp_re__chars) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF_DOT_IndProp.LF.IndProp.re_chars) Original_LF__DOT__IndProp_LF_IndProp_re__chars_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_IndProp.LF.IndProp.re_chars) (@Imported.Original_LF__DOT__IndProp_LF_IndProp_re__chars) Original_LF__DOT__IndProp_LF_IndProp_re__chars_iso := {}.