From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.

Monomorphic Definition imported_Original_LF__DOT__AltAuto_LF_AltAuto_re__opt__e : forall x : Type, imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp x -> imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp x := (@Imported.Original_LF__DOT__AltAuto_LF_AltAuto_re__opt__e).

Lemma re_opt_e_to_eq : forall (x1 x2 : Type) (hx : Iso x1 x2) (re : Original.LF_DOT_IndProp.LF.IndProp.reg_exp x1),
  IsomorphismDefinitions.eq
    (to (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) (Original.LF_DOT_AltAuto.LF.AltAuto.re_opt_e re))
    (imported_Original_LF__DOT__AltAuto_LF_AltAuto_re__opt__e (to (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) re)).
Proof.
  intros x1 x2 hx re.
  induction re; cbn -[to imported_Original_LF__DOT__AltAuto_LF_AltAuto_re__opt__e].
  - cbn. apply IsomorphismDefinitions.eq_refl.
  - cbn. apply IsomorphismDefinitions.eq_refl.
  - cbn. apply IsomorphismDefinitions.eq_refl.
  - destruct re1; cbn.
    + apply f_equal2; [apply IsomorphismDefinitions.eq_refl | apply IHre2].
    + apply IHre2.
    + apply f_equal2; [apply IsomorphismDefinitions.eq_refl | apply IHre2].
    + apply f_equal2; [apply IHre1 | apply IHre2].
    + apply f_equal2; [apply IHre1 | apply IHre2].
    + apply f_equal2; [apply IHre1 | apply IHre2].
  - cbn. apply f_equal2; [apply IHre1 | apply IHre2].
  - cbn. apply f_equal; apply IHre.
Defined.

Monomorphic Instance Original_LF__DOT__AltAuto_LF_AltAuto_re__opt__e_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_IndProp.LF.IndProp.reg_exp x1) (x4 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp x2),
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) x3 x4 ->
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) (Original.LF_DOT_AltAuto.LF.AltAuto.re_opt_e x3) (imported_Original_LF__DOT__AltAuto_LF_AltAuto_re__opt__e x4).
Proof.
  intros x1 x2 hx x3 x4 Hrel.
  destruct Hrel as [Hto_eq].
  constructor.
  eapply eq_trans. apply re_opt_e_to_eq.
  apply f_equal. exact Hto_eq.
Defined.
Instance: KnownConstant (@Original.LF_DOT_AltAuto.LF.AltAuto.re_opt_e) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Original_LF__DOT__AltAuto_LF_AltAuto_re__opt__e) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF_DOT_AltAuto.LF.AltAuto.re_opt_e) Original_LF__DOT__AltAuto_LF_AltAuto_re__opt__e_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_AltAuto.LF.AltAuto.re_opt_e) (@Imported.Original_LF__DOT__AltAuto_LF_AltAuto_re__opt__e) Original_LF__DOT__AltAuto_LF_AltAuto_re__opt__e_iso := {}.