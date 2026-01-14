From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_result : Type := Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_result.

Definition result_to_imported (r : Original.LF_DOT_Imp.LF.Imp.BreakImp.result) : Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_result :=
  match r with
  | Original.LF_DOT_Imp.LF.Imp.BreakImp.SContinue => Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_result_SContinue
  | Original.LF_DOT_Imp.LF.Imp.BreakImp.SBreak => Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_result_SBreak
  end.

Definition imported_to_result (r : Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_result) : Original.LF_DOT_Imp.LF.Imp.BreakImp.result :=
  match r with
  | Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_result_SContinue => Original.LF_DOT_Imp.LF.Imp.BreakImp.SContinue
  | Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_result_SBreak => Original.LF_DOT_Imp.LF.Imp.BreakImp.SBreak
  end.

Definition result_roundtrip1 (r : Original.LF_DOT_Imp.LF.Imp.BreakImp.result) : @Logic.eq _ (imported_to_result (result_to_imported r)) r :=
  match r with
  | Original.LF_DOT_Imp.LF.Imp.BreakImp.SContinue => Logic.eq_refl
  | Original.LF_DOT_Imp.LF.Imp.BreakImp.SBreak => Logic.eq_refl
  end.

Definition result_roundtrip2 (r : Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_result) : @Logic.eq _ (result_to_imported (imported_to_result r)) r :=
  match r with
  | Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_result_SContinue => Logic.eq_refl
  | Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_result_SBreak => Logic.eq_refl
  end.

Instance Original_LF__DOT__Imp_LF_Imp_BreakImp_result_iso : Iso Original.LF_DOT_Imp.LF.Imp.BreakImp.result imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_result.
Proof.
  exact (Build_Iso result_to_imported imported_to_result
    (fun r => seq_of_eq (result_roundtrip2 r))
    (fun r => seq_of_eq (result_roundtrip1 r))).
Defined.
Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.BreakImp.result := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_result := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.BreakImp.result Original_LF__DOT__Imp_LF_Imp_BreakImp_result_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.BreakImp.result Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_result Original_LF__DOT__Imp_LF_Imp_BreakImp_result_iso := {}.