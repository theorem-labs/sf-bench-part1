From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__bexp__iso.

Definition imported_Original_LF__DOT__Imp_LF_Imp_com : Type := Imported.Original_LF__DOT__Imp_LF_Imp_com.

Fixpoint com_to_imported (c : Original.LF_DOT_Imp.LF.Imp.com) : imported_Original_LF__DOT__Imp_LF_Imp_com :=
  match c with
  | Original.LF_DOT_Imp.LF.Imp.CSkip => Imported.Original_LF__DOT__Imp_LF_Imp_com_CSkip
  | Original.LF_DOT_Imp.LF.Imp.CAsgn x a => Imported.Original_LF__DOT__Imp_LF_Imp_com_CAsgn (to_string x) (aexp_to_imported a)
  | Original.LF_DOT_Imp.LF.Imp.CSeq c1 c2 => Imported.Original_LF__DOT__Imp_LF_Imp_com_CSeq (com_to_imported c1) (com_to_imported c2)
  | Original.LF_DOT_Imp.LF.Imp.CIf b c1 c2 => Imported.Original_LF__DOT__Imp_LF_Imp_com_CIf (bexp_to_imported b) (com_to_imported c1) (com_to_imported c2)
  | Original.LF_DOT_Imp.LF.Imp.CWhile b c1 => Imported.Original_LF__DOT__Imp_LF_Imp_com_CWhile (bexp_to_imported b) (com_to_imported c1)
  end.

Fixpoint com_from_imported (c : imported_Original_LF__DOT__Imp_LF_Imp_com) : Original.LF_DOT_Imp.LF.Imp.com :=
  match c with
  | Imported.Original_LF__DOT__Imp_LF_Imp_com_CSkip => Original.LF_DOT_Imp.LF.Imp.CSkip
  | Imported.Original_LF__DOT__Imp_LF_Imp_com_CAsgn x a => Original.LF_DOT_Imp.LF.Imp.CAsgn (from_string x) (aexp_from_imported a)
  | Imported.Original_LF__DOT__Imp_LF_Imp_com_CSeq c1 c2 => Original.LF_DOT_Imp.LF.Imp.CSeq (com_from_imported c1) (com_from_imported c2)
  | Imported.Original_LF__DOT__Imp_LF_Imp_com_CIf b c1 c2 => Original.LF_DOT_Imp.LF.Imp.CIf (bexp_from_imported b) (com_from_imported c1) (com_from_imported c2)
  | Imported.Original_LF__DOT__Imp_LF_Imp_com_CWhile b c1 => Original.LF_DOT_Imp.LF.Imp.CWhile (bexp_from_imported b) (com_from_imported c1)
  end.

Lemma com_to_from : forall c, eq (com_to_imported (com_from_imported c)) c.
Proof.
  fix to_from 1.
  intros c.
  destruct c; simpl.
  - apply eq_refl.
  - apply (IsoEq.f_equal2 Imported.Original_LF__DOT__Imp_LF_Imp_com_CAsgn).
    + apply to_from_string.
    + apply aexp_to_from.
  - apply (IsoEq.f_equal2 Imported.Original_LF__DOT__Imp_LF_Imp_com_CSeq); apply to_from.
  - apply (IsoEq.f_equal3 Imported.Original_LF__DOT__Imp_LF_Imp_com_CIf).
    + apply bexp_to_from.
    + apply to_from.
    + apply to_from.
  - apply (IsoEq.f_equal2 Imported.Original_LF__DOT__Imp_LF_Imp_com_CWhile).
    + apply bexp_to_from.
    + apply to_from.
Qed.

Lemma com_from_to : forall c, eq (com_from_imported (com_to_imported c)) c.
Proof.
  fix from_to 1.
  intros c.
  destruct c; simpl.
  - apply eq_refl.
  - apply (IsoEq.f_equal2 Original.LF_DOT_Imp.LF.Imp.CAsgn).
    + apply from_to_string.
    + apply aexp_from_to.
  - apply (IsoEq.f_equal2 Original.LF_DOT_Imp.LF.Imp.CSeq); apply from_to.
  - apply (IsoEq.f_equal3 Original.LF_DOT_Imp.LF.Imp.CIf).
    + apply bexp_from_to.
    + apply from_to.
    + apply from_to.
  - apply (IsoEq.f_equal2 Original.LF_DOT_Imp.LF.Imp.CWhile).
    + apply bexp_from_to.
    + apply from_to.
Qed.

Instance Original_LF__DOT__Imp_LF_Imp_com_iso : Iso Original.LF_DOT_Imp.LF.Imp.com imported_Original_LF__DOT__Imp_LF_Imp_com :=
  {| to := com_to_imported; from := com_from_imported; to_from := com_to_from; from_to := com_from_to |}.

Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.com := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_com := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.com Original_LF__DOT__Imp_LF_Imp_com_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.com Imported.Original_LF__DOT__Imp_LF_Imp_com Original_LF__DOT__Imp_LF_Imp_com_iso := {}.
