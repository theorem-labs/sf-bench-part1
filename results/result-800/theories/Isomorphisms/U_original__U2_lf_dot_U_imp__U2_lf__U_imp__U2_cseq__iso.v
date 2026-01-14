From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso.
Typeclasses Opaque rel_iso. (* for speed *)

Notation imported_Original_LF__DOT__Imp_LF_Imp_CSeq := Imported.Original_LF__DOT__Imp_LF_Imp_CSeq.

Instance Original_LF__DOT__Imp_LF_Imp_CSeq_iso : forall (x1 : Original.LF_DOT_Imp.LF.Imp.com) (x2 : imported_Original_LF__DOT__Imp_LF_Imp_com),
  rel_iso Original_LF__DOT__Imp_LF_Imp_com_iso x1 x2 ->
  forall (x3 : Original.LF_DOT_Imp.LF.Imp.com) (x4 : imported_Original_LF__DOT__Imp_LF_Imp_com),
  rel_iso Original_LF__DOT__Imp_LF_Imp_com_iso x3 x4 -> rel_iso Original_LF__DOT__Imp_LF_Imp_com_iso (Original.LF_DOT_Imp.LF.Imp.CSeq x1 x3) (imported_Original_LF__DOT__Imp_LF_Imp_CSeq x2 x4).
Proof.
  intros x1 x2 H1 x3 x4 H2.
  unfold rel_iso in *.
  unfold com_to_imported.
  simpl.
  unfold imported_Original_LF__DOT__Imp_LF_Imp_CSeq.
  unfold Imported.Original_LF__DOT__Imp_LF_Imp_CSeq.
  apply f_equal2; assumption.
Qed.

Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.CSeq := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant imported_Original_LF__DOT__Imp_LF_Imp_CSeq := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.CSeq Original_LF__DOT__Imp_LF_Imp_CSeq_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.CSeq imported_Original_LF__DOT__Imp_LF_Imp_CSeq Original_LF__DOT__Imp_LF_Imp_CSeq_iso := {}.
