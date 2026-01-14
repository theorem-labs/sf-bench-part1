From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__com__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__bexp__iso.

Definition imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_CWhile : imported_Original_LF__DOT__Imp_LF_Imp_bexp -> imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_com -> imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_com := Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_CWhile.

(* Helper for f_equal2 using IsoEq.f_equal and eq_trans *)
Lemma f_equal2_helper : forall {A B C : Type} (f : A -> B -> C) (x1 x2 : A) (y1 y2 : B),
  IsomorphismDefinitions.eq x1 x2 -> IsomorphismDefinitions.eq y1 y2 -> 
  IsomorphismDefinitions.eq (f x1 y1) (f x2 y2).
Proof.
  intros A B C f x1 x2 y1 y2 Hx Hy.
  pose proof (@IsoEq.f_equal A C (fun a => f a y1) x1 x2 Hx) as E1.
  pose proof (@IsoEq.f_equal B C (f x2) y1 y2 Hy) as E2.
  exact (@IsoEq.eq_trans C _ _ _ E1 E2).
Defined.

Instance Original_LF__DOT__Imp_LF_Imp_BreakImp_CWhile_iso : forall (x1 : Original.LF_DOT_Imp.LF.Imp.bexp) (x2 : imported_Original_LF__DOT__Imp_LF_Imp_bexp),
  rel_iso Original_LF__DOT__Imp_LF_Imp_bexp_iso x1 x2 ->
  forall (x3 : Original.LF_DOT_Imp.LF.Imp.BreakImp.com) (x4 : imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_com),
  rel_iso Original_LF__DOT__Imp_LF_Imp_BreakImp_com_iso x3 x4 ->
  rel_iso Original_LF__DOT__Imp_LF_Imp_BreakImp_com_iso (Original.LF_DOT_Imp.LF.Imp.BreakImp.CWhile x1 x3) (imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_CWhile x2 x4).
Proof.
  intros x1 x2 H1 x3 x4 H2.
  unfold rel_iso in *.
  unfold imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_CWhile.
  unfold Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_CWhile.
  simpl.
  apply f_equal2_helper; assumption.
Defined.
Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.BreakImp.CWhile := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_CWhile := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.BreakImp.CWhile Original_LF__DOT__Imp_LF_Imp_BreakImp_CWhile_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.BreakImp.CWhile Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_CWhile Original_LF__DOT__Imp_LF_Imp_BreakImp_CWhile_iso := {}.