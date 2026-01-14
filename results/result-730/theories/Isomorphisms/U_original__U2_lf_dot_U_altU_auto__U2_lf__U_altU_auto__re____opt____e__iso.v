From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

#[local] Notation "x = y" := (IsomorphismDefinitions.eq x y) : type_scope.

From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.

Definition imported_Original_LF__DOT__AltAuto_LF_AltAuto_re__opt__e : forall x : Type, imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp x -> imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp x := (@Imported.Original_LF__DOT__AltAuto_LF_AltAuto_re__opt__e).

(* Helper to convert between Original and Imported reg_exp *)
Definition to_imported {T1 T2} (isoT : Iso T1 T2) : Original.LF_DOT_IndProp.LF.IndProp.reg_exp T1 -> imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp T2 :=
  fix f (re : Original.LF_DOT_IndProp.LF.IndProp.reg_exp T1) : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp T2 :=
    match re with
    | Original.LF_DOT_IndProp.LF.IndProp.EmptySet => Imported.Original_LF__DOT__IndProp_LF_IndProp_reg__exp_EmptySet T2
    | Original.LF_DOT_IndProp.LF.IndProp.EmptyStr => Imported.Original_LF__DOT__IndProp_LF_IndProp_reg__exp_EmptyStr T2
    | Original.LF_DOT_IndProp.LF.IndProp.Char t => Imported.Original_LF__DOT__IndProp_LF_IndProp_reg__exp_Char T2 (to isoT t)
    | Original.LF_DOT_IndProp.LF.IndProp.App r1 r2 => Imported.Original_LF__DOT__IndProp_LF_IndProp_reg__exp_App T2 (f r1) (f r2)
    | Original.LF_DOT_IndProp.LF.IndProp.Union r1 r2 => Imported.Original_LF__DOT__IndProp_LF_IndProp_reg__exp_Union T2 (f r1) (f r2)
    | Original.LF_DOT_IndProp.LF.IndProp.Star r => Imported.Original_LF__DOT__IndProp_LF_IndProp_reg__exp_Star T2 (f r)
    end.

(* Key lemma: to_imported commutes with re_opt_e *)
Lemma re_opt_e_commutes : forall T1 T2 (isoT : Iso T1 T2) (re : Original.LF_DOT_IndProp.LF.IndProp.reg_exp T1),
  to_imported isoT (Original.LF_DOT_AltAuto.LF.AltAuto.re_opt_e re) =
  Imported.Original_LF__DOT__AltAuto_LF_AltAuto_re__opt__e T2 (to_imported isoT re).
Proof.
  intros T1 T2 isoT re.
  induction re as [| | t | re1 IHre1 re2 IHre2 | re1 IHre1 re2 IHre2 | re1 IHre1 ].
  - (* EmptySet *) reflexivity.
  - (* EmptyStr *) reflexivity.
  - (* Char *) reflexivity.
  - (* App case *)
    destruct re1 as [| | t' | re1a re1b | re1a re1b | re1a ]; cbn [Original.LF_DOT_AltAuto.LF.AltAuto.re_opt_e to_imported].
    + (* EmptySet *) cbn. exact (f_equal _ IHre2).
    + (* EmptyStr *) exact IHre2.
    + (* Char *) cbn. exact (f_equal2 _ IHre1 IHre2).
    + (* App *) cbn. exact (f_equal2 _ IHre1 IHre2).
    + (* Union *) cbn. exact (f_equal2 _ IHre1 IHre2).
    + (* Star *) cbn. exact (f_equal2 _ IHre1 IHre2).
  - (* Union case *)
    cbn. exact (f_equal2 _ IHre1 IHre2).
  - (* Star case *)
    cbn. exact (f_equal _ IHre1).
Qed.

(* The to function of the reg_exp isomorphism is to_imported *)
Lemma to_iso_is_to_imported : forall T1 T2 (isoT : Iso T1 T2) (re : Original.LF_DOT_IndProp.LF.IndProp.reg_exp T1),
  to (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso isoT) re = to_imported isoT re.
Proof.
  intros T1 T2 isoT re.
  induction re; simpl; try reflexivity;
  try (exact (f_equal2 _ IHre1 IHre2));
  try (exact (f_equal _ IHre)).
Qed.

Instance Original_LF__DOT__AltAuto_LF_AltAuto_re__opt__e_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_IndProp.LF.IndProp.reg_exp x1) (x4 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp x2),
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) x3 x4 ->
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) (Original.LF_DOT_AltAuto.LF.AltAuto.re_opt_e x3) (imported_Original_LF__DOT__AltAuto_LF_AltAuto_re__opt__e x4).
Proof.
  intros x1 x2 hx x3 x4 H.
  unfold rel_iso in *.
  pose proof (@to_iso_is_to_imported x1 x2 hx x3) as E1.
  pose proof (@to_iso_is_to_imported x1 x2 hx (Original.LF_DOT_AltAuto.LF.AltAuto.re_opt_e x3)) as E2.
  pose proof (@re_opt_e_commutes x1 x2 hx x3) as E3.
  unfold imported_Original_LF__DOT__AltAuto_LF_AltAuto_re__opt__e.
  eapply eq_trans. exact E2.
  eapply eq_trans. exact E3.
  apply f_equal.
  eapply eq_trans. 2: exact H.
  apply eq_sym.
  exact E1.
Defined.
Instance: KnownConstant (@Original.LF_DOT_AltAuto.LF.AltAuto.re_opt_e) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Original_LF__DOT__AltAuto_LF_AltAuto_re__opt__e) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF_DOT_AltAuto.LF.AltAuto.re_opt_e) Original_LF__DOT__AltAuto_LF_AltAuto_re__opt__e_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_AltAuto.LF.AltAuto.re_opt_e) (@Imported.Original_LF__DOT__AltAuto_LF_AltAuto_re__opt__e) Original_LF__DOT__AltAuto_LF_AltAuto_re__opt__e_iso := {}.