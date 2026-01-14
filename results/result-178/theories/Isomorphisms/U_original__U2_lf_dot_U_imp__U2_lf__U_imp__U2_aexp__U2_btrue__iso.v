From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

#[local] Notation "x = y" := (IsomorphismDefinitions.eq x y) : type_scope.

From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__bexp__iso.

Definition imported_Original_LF__DOT__Imp_LF_Imp_AExp_BTrue : imported_Original_LF__DOT__Imp_LF_Imp_AExp_bexp := Imported.Original_LF__DOT__Imp_LF_Imp_AExp_BTrue.

(* The rel_iso for BTrue is: bexp_to_imported BTrue = imported_BTrue *)
(* which is: Imported.Original_LF__DOT__Imp_LF_Imp_AExp_bexp_BTrue = Imported.Original_LF__DOT__Imp_LF_Imp_AExp_BTrue *)
(* Both are definitionally equal to BTrue constructor *)
Instance Original_LF__DOT__Imp_LF_Imp_AExp_BTrue_iso : rel_iso Original_LF__DOT__Imp_LF_Imp_AExp_bexp_iso Original.LF_DOT_Imp.LF.Imp.AExp.BTrue imported_Original_LF__DOT__Imp_LF_Imp_AExp_BTrue.
Proof.
  unfold rel_iso.
  unfold imported_Original_LF__DOT__Imp_LF_Imp_AExp_BTrue.
  simpl.
  apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.AExp.BTrue := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_AExp_BTrue := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.AExp.BTrue Original_LF__DOT__Imp_LF_Imp_AExp_BTrue_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.AExp.BTrue Imported.Original_LF__DOT__Imp_LF_Imp_AExp_BTrue Original_LF__DOT__Imp_LF_Imp_AExp_BTrue_iso := {}.