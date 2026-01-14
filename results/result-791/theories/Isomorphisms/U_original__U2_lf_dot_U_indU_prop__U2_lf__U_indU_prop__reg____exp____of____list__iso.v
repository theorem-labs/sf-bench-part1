From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp__of__list : forall x : Type, imported_Original_LF__DOT__Poly_LF_Poly_list x -> imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp x := (@Imported.Original_LF__DOT__IndProp_LF_IndProp_reg__exp__of__list).

(* Helper lemmas for the imported reg_exp_of_list computation *)
Lemma Imported_reg_exp_of_list_nil : forall (x2 : Type),
  IsomorphismDefinitions.eq
    (Imported.Original_LF__DOT__IndProp_LF_IndProp_reg__exp__of__list x2 (Imported.Original_LF__DOT__Poly_LF_Poly_list_nil x2))
    (Imported.Original_LF__DOT__IndProp_LF_IndProp_reg__exp_EmptyStr x2).
Proof.
  intros x2.
  unfold Imported.Original_LF__DOT__IndProp_LF_IndProp_reg__exp__of__list.
  simpl.
  apply IsomorphismDefinitions.eq_refl.
Qed.

Lemma Imported_reg_exp_of_list_cons : forall (x2 : Type) (h : x2) (t : Imported.Original_LF__DOT__Poly_LF_Poly_list x2),
  IsomorphismDefinitions.eq
    (Imported.Original_LF__DOT__IndProp_LF_IndProp_reg__exp__of__list x2 (Imported.Original_LF__DOT__Poly_LF_Poly_list_cons x2 h t))
    (Imported.Original_LF__DOT__IndProp_LF_IndProp_reg__exp_App x2 
      (Imported.Original_LF__DOT__IndProp_LF_IndProp_reg__exp_Char x2 h)
      (Imported.Original_LF__DOT__IndProp_LF_IndProp_reg__exp__of__list x2 t)).
Proof.
  intros x2 h t.
  unfold Imported.Original_LF__DOT__IndProp_LF_IndProp_reg__exp__of__list.
  simpl.
  apply IsomorphismDefinitions.eq_refl.
Qed.

(* Commutation lemma: the isomorphisms commute with reg_exp_of_list *)
Lemma reg_exp_of_list_commutes : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_Poly.LF.Poly.list x1),
  IsomorphismDefinitions.eq
    (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx (Original.LF_DOT_IndProp.LF.IndProp.reg_exp_of_list x3))
    (Imported.Original_LF__DOT__IndProp_LF_IndProp_reg__exp__of__list x2 (Original_LF__DOT__Poly_LF_Poly_list_iso hx x3)).
Proof.
  intros x1 x2 hx.
  fix IH 1.
  intro x3.
  destruct x3 as [|h t].
  { (* nil case *)
    simpl.
    exact (IsoEq.eq_sym (Imported_reg_exp_of_list_nil x2)). }
  { (* cons case *)
    simpl.
    apply (IsoEq.f_equal2 (Imported.Original_LF__DOT__IndProp_LF_IndProp_reg__exp_App x2)).
    { apply IsomorphismDefinitions.eq_refl. }
    { apply IH. } }
Qed.

Instance Original_LF__DOT__IndProp_LF_IndProp_reg__exp__of__list_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_Poly.LF.Poly.list x1) (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x3 x4 ->
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) (Original.LF_DOT_IndProp.LF.IndProp.reg_exp_of_list x3) (imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp__of__list x4).
Proof.
  intros x1 x2 hx x3 x4 H34.
  unfold rel_iso in *.
  unfold imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp__of__list.
  apply (IsoEq.eq_trans (reg_exp_of_list_commutes hx x3)).
  apply (IsoEq.f_equal (Imported.Original_LF__DOT__IndProp_LF_IndProp_reg__exp__of__list x2)).
  exact H34.
Qed.
Instance: KnownConstant (@Original.LF_DOT_IndProp.LF.IndProp.reg_exp_of_list) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Original_LF__DOT__IndProp_LF_IndProp_reg__exp__of__list) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF_DOT_IndProp.LF.IndProp.reg_exp_of_list) Original_LF__DOT__IndProp_LF_IndProp_reg__exp__of__list_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_IndProp.LF.IndProp.reg_exp_of_list) (@Imported.Original_LF__DOT__IndProp_LF_IndProp_reg__exp__of__list) Original_LF__DOT__IndProp_LF_IndProp_reg__exp__of__list_iso := {}.