From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso.

Monomorphic Definition imported_Original_LF__DOT__IndProp_LF_IndProp_re__chars : forall x : Type, imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp x -> imported_Original_LF__DOT__Poly_LF_Poly_list x := (@Imported.Original_LF__DOT__IndProp_LF_IndProp_re__chars).

Lemma re_chars_to_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_IndProp.LF.IndProp.reg_exp x1),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) 
    (Original.LF_DOT_IndProp.LF.IndProp.re_chars x3) 
    (imported_Original_LF__DOT__IndProp_LF_IndProp_re__chars (to (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) x3)).
Proof.
  intros x1 x2 hx x3.
  induction x3 as [| | t | x3_1 IH1 x3_2 IH2 | x3_1 IH1 x3_2 IH2 | x3 IH]; simpl.
  - apply Original_LF__DOT__Poly_LF_Poly_nil_iso.
  - apply Original_LF__DOT__Poly_LF_Poly_nil_iso.
  - apply Original_LF__DOT__Poly_LF_Poly_cons_iso; [apply rel_iso_refl | apply Original_LF__DOT__Poly_LF_Poly_nil_iso].
  - apply Original_LF__DOT__Poly_LF_Poly_app_iso; [exact IH1 | exact IH2].
  - apply Original_LF__DOT__Poly_LF_Poly_app_iso; [exact IH1 | exact IH2].
  - exact IH.
Defined.

Monomorphic Instance Original_LF__DOT__IndProp_LF_IndProp_re__chars_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_IndProp.LF.IndProp.reg_exp x1) (x4 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp x2),
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) x3 x4 ->
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) (Original.LF_DOT_IndProp.LF.IndProp.re_chars x3) (imported_Original_LF__DOT__IndProp_LF_IndProp_re__chars x4).
Proof.
  intros x1 x2 hx x3 x4 Hiso.
  pose proof (proj_rel_iso Hiso) as Heq.
  apply eq_of_seq in Heq.
  rewrite <- Heq.
  apply re_chars_to_iso.
Defined.
Instance: KnownConstant (@Original.LF_DOT_IndProp.LF.IndProp.re_chars) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Original_LF__DOT__IndProp_LF_IndProp_re__chars) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF_DOT_IndProp.LF.IndProp.re_chars) Original_LF__DOT__IndProp_LF_IndProp_re__chars_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_IndProp.LF.IndProp.re_chars) (@Imported.Original_LF__DOT__IndProp_LF_IndProp_re__chars) Original_LF__DOT__IndProp_LF_IndProp_re__chars_iso := {}.