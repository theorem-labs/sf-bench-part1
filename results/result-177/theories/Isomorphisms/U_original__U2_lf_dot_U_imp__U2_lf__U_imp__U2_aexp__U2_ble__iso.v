From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__aexp__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__bexp__iso.

Definition imported_Original_LF__DOT__Imp_LF_Imp_AExp_BLe : imported_Original_LF__DOT__Imp_LF_Imp_AExp_aexp -> imported_Original_LF__DOT__Imp_LF_Imp_AExp_aexp -> imported_Original_LF__DOT__Imp_LF_Imp_AExp_bexp := Imported.Original_LF__DOT__Imp_LF_Imp_AExp_BLe.
Instance Original_LF__DOT__Imp_LF_Imp_AExp_BLe_iso : forall (x1 : Original.LF_DOT_Imp.LF.Imp.AExp.aexp) (x2 : imported_Original_LF__DOT__Imp_LF_Imp_AExp_aexp),
  rel_iso Original_LF__DOT__Imp_LF_Imp_AExp_aexp_iso x1 x2 ->
  forall (x3 : Original.LF_DOT_Imp.LF.Imp.AExp.aexp) (x4 : imported_Original_LF__DOT__Imp_LF_Imp_AExp_aexp),
  rel_iso Original_LF__DOT__Imp_LF_Imp_AExp_aexp_iso x3 x4 ->
  rel_iso Original_LF__DOT__Imp_LF_Imp_AExp_bexp_iso (Original.LF_DOT_Imp.LF.Imp.AExp.BLe x1 x3) (imported_Original_LF__DOT__Imp_LF_Imp_AExp_BLe x2 x4).
Proof.
  intros x1 x2 H1 x3 x4 H2.
  unfold rel_iso in *.
  unfold imported_Original_LF__DOT__Imp_LF_Imp_AExp_BLe.
  unfold Imported.Original_LF__DOT__Imp_LF_Imp_AExp_BLe.
  (* to Original_LF__DOT__Imp_LF_Imp_AExp_bexp_iso (BLe x1 x3) = BLe x2 x4 *)
  simpl.
  (* Need to show: BLe (to aexp_iso x1) (to aexp_iso x3) = BLe x2 x4 *)
  (* By H1: to aexp_iso x1 = x2 *)
  (* By H2: to aexp_iso x3 = x4 *)
  apply (IsoEq.f_equal2 Imported.Original_LF__DOT__Imp_LF_Imp_AExp_bexp_BLe H1 H2).
Defined.
Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.AExp.BLe := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_AExp_BLe := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.AExp.BLe Original_LF__DOT__Imp_LF_Imp_AExp_BLe_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.AExp.BLe Imported.Original_LF__DOT__Imp_LF_Imp_AExp_BLe Original_LF__DOT__Imp_LF_Imp_AExp_BLe_iso := {}.