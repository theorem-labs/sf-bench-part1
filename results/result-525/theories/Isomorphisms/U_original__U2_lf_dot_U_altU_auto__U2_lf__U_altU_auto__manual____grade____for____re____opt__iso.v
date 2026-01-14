From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__string__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__option__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__prod__iso Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__AltAuto_LF_AltAuto_manual__grade__for__re__opt : imported_Original_LF__DOT__Poly_LF_Poly_option (imported_Original_LF__DOT__Poly_LF_Poly_prod imported_nat (imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii)) := Imported.Original_LF__DOT__AltAuto_LF_AltAuto_manual__grade__for__re__opt.
Instance Original_LF__DOT__AltAuto_LF_AltAuto_manual__grade__for__re__opt_iso : rel_iso (Original_LF__DOT__Poly_LF_Poly_option_iso (Original_LF__DOT__Poly_LF_Poly_prod_iso nat_iso (Original_LF__DOT__Poly_LF_Poly_list_iso Ascii_ascii_iso)))
    Original.LF_DOT_AltAuto.LF.AltAuto.manual_grade_for_re_opt imported_Original_LF__DOT__AltAuto_LF_AltAuto_manual__grade__for__re__opt.
Proof.
  (* Both sides are None, so they should be equal under the isomorphism *)
  unfold rel_iso.
  unfold imported_Original_LF__DOT__AltAuto_LF_AltAuto_manual__grade__for__re__opt.
  simpl.
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_AltAuto.LF.AltAuto.manual_grade_for_re_opt := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__AltAuto_LF_AltAuto_manual__grade__for__re__opt := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_AltAuto.LF.AltAuto.manual_grade_for_re_opt Original_LF__DOT__AltAuto_LF_AltAuto_manual__grade__for__re__opt_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_AltAuto.LF.AltAuto.manual_grade_for_re_opt Imported.Original_LF__DOT__AltAuto_LF_AltAuto_manual__grade__for__re__opt Original_LF__DOT__AltAuto_LF_AltAuto_manual__grade__for__re__opt_iso := {}.