From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aexp__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__bexp__iso.

Definition imported_Original_LF__DOT__Imp_LF_Imp_com : Type := Imported.Original_LF__DOT__Imp_LF_Imp_com.

Fixpoint com_to_imported (c : Original.LF_DOT_Imp.LF.Imp.com) : imported_Original_LF__DOT__Imp_LF_Imp_com :=
  match c with
  | Original.LF_DOT_Imp.LF.Imp.CSkip => Imported.Original_LF__DOT__Imp_LF_Imp_com_CSkip
  | Original.LF_DOT_Imp.LF.Imp.CAsgn x a => Imported.Original_LF__DOT__Imp_LF_Imp_com_CAsgn (string_to_String_string x) (aexp_to_imported a)
  | Original.LF_DOT_Imp.LF.Imp.CSeq c1 c2 => Imported.Original_LF__DOT__Imp_LF_Imp_com_CSeq (com_to_imported c1) (com_to_imported c2)
  | Original.LF_DOT_Imp.LF.Imp.CIf b c1 c2 => Imported.Original_LF__DOT__Imp_LF_Imp_com_CIf (bexp_to_imported b) (com_to_imported c1) (com_to_imported c2)
  | Original.LF_DOT_Imp.LF.Imp.CWhile b c => Imported.Original_LF__DOT__Imp_LF_Imp_com_CWhile (bexp_to_imported b) (com_to_imported c)
  end.

Fixpoint com_from_imported (c : imported_Original_LF__DOT__Imp_LF_Imp_com) : Original.LF_DOT_Imp.LF.Imp.com :=
  match c with
  | Imported.Original_LF__DOT__Imp_LF_Imp_com_CSkip => Original.LF_DOT_Imp.LF.Imp.CSkip
  | Imported.Original_LF__DOT__Imp_LF_Imp_com_CAsgn x a => Original.LF_DOT_Imp.LF.Imp.CAsgn (String_string_to_string x) (aexp_from_imported a)
  | Imported.Original_LF__DOT__Imp_LF_Imp_com_CSeq c1 c2 => Original.LF_DOT_Imp.LF.Imp.CSeq (com_from_imported c1) (com_from_imported c2)
  | Imported.Original_LF__DOT__Imp_LF_Imp_com_CIf b c1 c2 => Original.LF_DOT_Imp.LF.Imp.CIf (bexp_from_imported b) (com_from_imported c1) (com_from_imported c2)
  | Imported.Original_LF__DOT__Imp_LF_Imp_com_CWhile b c => Original.LF_DOT_Imp.LF.Imp.CWhile (bexp_from_imported b) (com_from_imported c)
  end.

Instance Original_LF__DOT__Imp_LF_Imp_com_iso : Iso Original.LF_DOT_Imp.LF.Imp.com imported_Original_LF__DOT__Imp_LF_Imp_com.
Proof.
  unshelve eapply Build_Iso.
  - exact com_to_imported.
  - exact com_from_imported.
  - fix to_from 1. intro c. destruct c; simpl.
    + apply IsomorphismDefinitions.eq_refl.
    + apply (IsoEq.f_equal2 Imported.Original_LF__DOT__Imp_LF_Imp_com_CAsgn).
      * apply (@IsomorphismDefinitions.to_from _ _ String_string_iso).
      * apply (@IsomorphismDefinitions.to_from _ _ Original_LF__DOT__Imp_LF_Imp_aexp_iso).
    + apply (IsoEq.f_equal2 Imported.Original_LF__DOT__Imp_LF_Imp_com_CSeq); apply to_from.
    + apply (IsoEq.f_equal3 Imported.Original_LF__DOT__Imp_LF_Imp_com_CIf).
      * apply (@IsomorphismDefinitions.to_from _ _ Original_LF__DOT__Imp_LF_Imp_bexp_iso).
      * apply to_from.
      * apply to_from.
    + apply (IsoEq.f_equal2 Imported.Original_LF__DOT__Imp_LF_Imp_com_CWhile).
      * apply (@IsomorphismDefinitions.to_from _ _ Original_LF__DOT__Imp_LF_Imp_bexp_iso).
      * apply to_from.
  - fix from_to 1. intro c. destruct c; simpl.
    + apply IsomorphismDefinitions.eq_refl.
    + apply (IsoEq.f_equal2 Original.LF_DOT_Imp.LF.Imp.CAsgn).
      * apply (@IsomorphismDefinitions.from_to _ _ String_string_iso).
      * apply (@IsomorphismDefinitions.from_to _ _ Original_LF__DOT__Imp_LF_Imp_aexp_iso).
    + apply (IsoEq.f_equal2 Original.LF_DOT_Imp.LF.Imp.CSeq); apply from_to.
    + apply (IsoEq.f_equal3 Original.LF_DOT_Imp.LF.Imp.CIf).
      * apply (@IsomorphismDefinitions.from_to _ _ Original_LF__DOT__Imp_LF_Imp_bexp_iso).
      * apply from_to.
      * apply from_to.
    + apply (IsoEq.f_equal2 Original.LF_DOT_Imp.LF.Imp.CWhile).
      * apply (@IsomorphismDefinitions.from_to _ _ Original_LF__DOT__Imp_LF_Imp_bexp_iso).
      * apply from_to.
Defined.

Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.com := {}.
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_com := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.com Original_LF__DOT__Imp_LF_Imp_com_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.com Imported.Original_LF__DOT__Imp_LF_Imp_com Original_LF__DOT__Imp_LF_Imp_com_iso := {}.