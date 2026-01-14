From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__bexp__iso.

Definition imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_com : Type := Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_com.

Fixpoint com_to_imported (c : Original.LF_DOT_Imp.LF.Imp.BreakImp.com) : Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_com :=
  match c with
  | Original.LF_DOT_Imp.LF.Imp.BreakImp.CSkip => Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_com_CSkip
  | Original.LF_DOT_Imp.LF.Imp.BreakImp.CBreak => Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_com_CBreak
  | Original.LF_DOT_Imp.LF.Imp.BreakImp.CAsgn x a => Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_com_CAsgn (to String_string_iso x) (aexp_to_imported a)
  | Original.LF_DOT_Imp.LF.Imp.BreakImp.CSeq c1 c2 => Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_com_CSeq (com_to_imported c1) (com_to_imported c2)
  | Original.LF_DOT_Imp.LF.Imp.BreakImp.CIf b c1 c2 => Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_com_CIf (bexp_to_imported b) (com_to_imported c1) (com_to_imported c2)
  | Original.LF_DOT_Imp.LF.Imp.BreakImp.CWhile b c => Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_com_CWhile (bexp_to_imported b) (com_to_imported c)
  end.

Fixpoint imported_to_com (c : Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_com) : Original.LF_DOT_Imp.LF.Imp.BreakImp.com :=
  match c with
  | Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_com_CSkip => Original.LF_DOT_Imp.LF.Imp.BreakImp.CSkip
  | Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_com_CBreak => Original.LF_DOT_Imp.LF.Imp.BreakImp.CBreak
  | Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_com_CAsgn x a => Original.LF_DOT_Imp.LF.Imp.BreakImp.CAsgn (from String_string_iso x) (imported_to_aexp a)
  | Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_com_CSeq c1 c2 => Original.LF_DOT_Imp.LF.Imp.BreakImp.CSeq (imported_to_com c1) (imported_to_com c2)
  | Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_com_CIf b c1 c2 => Original.LF_DOT_Imp.LF.Imp.BreakImp.CIf (imported_to_bexp b) (imported_to_com c1) (imported_to_com c2)
  | Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_com_CWhile b c => Original.LF_DOT_Imp.LF.Imp.BreakImp.CWhile (imported_to_bexp b) (imported_to_com c)
  end.

Definition com_roundtrip1 : forall c, @Logic.eq _ (imported_to_com (com_to_imported c)) c.
Proof.
  induction c as [| | x a | c1 IHc1 c2 IHc2 | b c1 IHc1 c2 IHc2 | b c IHc]; simpl.
  - exact Logic.eq_refl.
  - exact Logic.eq_refl.
  - exact (Logic.f_equal2 Original.LF_DOT_Imp.LF.Imp.BreakImp.CAsgn (sprop_to_prop (@from_to _ _ String_string_iso x)) (aexp_roundtrip1 a)).
  - exact (Logic.f_equal2 Original.LF_DOT_Imp.LF.Imp.BreakImp.CSeq IHc1 IHc2).
  - exact (Logic.f_equal3 Original.LF_DOT_Imp.LF.Imp.BreakImp.CIf (bexp_roundtrip1 b) IHc1 IHc2).
  - exact (Logic.f_equal2 Original.LF_DOT_Imp.LF.Imp.BreakImp.CWhile (bexp_roundtrip1 b) IHc).
Defined.

Definition com_roundtrip2 : forall c, @Logic.eq _ (com_to_imported (imported_to_com c)) c.
Proof.
  fix IH 1.
  intros c; destruct c as [| | x a | c1 c2 | b c1 c2 | b c]; simpl.
  - exact Logic.eq_refl.
  - exact Logic.eq_refl.
  - exact (Logic.f_equal2 Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_com_CAsgn (sprop_to_prop (@to_from _ _ String_string_iso x)) (aexp_roundtrip2 a)).
  - exact (Logic.f_equal2 Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_com_CSeq (IH c1) (IH c2)).
  - exact (Logic.f_equal3 Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_com_CIf (bexp_roundtrip2 b) (IH c1) (IH c2)).
  - exact (Logic.f_equal2 Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_com_CWhile (bexp_roundtrip2 b) (IH c)).
Defined.

Instance Original_LF__DOT__Imp_LF_Imp_BreakImp_com_iso : Iso Original.LF_DOT_Imp.LF.Imp.BreakImp.com imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_com.
Proof.
  exact (Build_Iso com_to_imported imported_to_com
    (fun c => seq_of_eq (com_roundtrip2 c))
    (fun c => seq_of_eq (com_roundtrip1 c))).
Defined.
Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.BreakImp.com := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_com := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.BreakImp.com Original_LF__DOT__Imp_LF_Imp_BreakImp_com_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.BreakImp.com Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_com Original_LF__DOT__Imp_LF_Imp_BreakImp_com_iso := {}.