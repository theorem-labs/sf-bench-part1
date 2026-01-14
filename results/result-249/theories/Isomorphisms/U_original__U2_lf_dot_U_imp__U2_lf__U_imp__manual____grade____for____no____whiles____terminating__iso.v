From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_string__string__iso Isomorphisms.nat__iso Isomorphisms.option__iso Isomorphisms.prod__iso.

Definition imported_Original_LF__DOT__Imp_LF_Imp_manual__grade__for__no__whiles__terminating : imported_option (imported_prod imported_nat imported_String_string) := Imported.Original_LF__DOT__Imp_LF_Imp_manual__grade__for__no__whiles__terminating.

Instance Original_LF__DOT__Imp_LF_Imp_manual__grade__for__no__whiles__terminating_iso : rel_iso (option_iso (prod_iso nat_iso String_string_iso)) Original.LF_DOT_Imp.LF.Imp.manual_grade_for_no_whiles_terminating
    imported_Original_LF__DOT__Imp_LF_Imp_manual__grade__for__no__whiles__terminating.
Proof.
  (* Original.LF_DOT_Imp.LF.Imp.manual_grade_for_no_whiles_terminating = None : option (nat * string) *)
  (* imported_Original_LF__DOT__Imp_LF_Imp_manual__grade__for__no__whiles__terminating = Imported.option_none (Imported.prod Imported.nat Imported.String_string) *)
  (* We need to show that the iso maps None to option_none *)
  unfold imported_Original_LF__DOT__Imp_LF_Imp_manual__grade__for__no__whiles__terminating.
  unfold Original.LF_DOT_Imp.LF.Imp.manual_grade_for_no_whiles_terminating.
  (* The original is None, and to iso on None gives option_none *)
  simpl.
  apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.manual_grade_for_no_whiles_terminating := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_manual__grade__for__no__whiles__terminating := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.manual_grade_for_no_whiles_terminating Original_LF__DOT__Imp_LF_Imp_manual__grade__for__no__whiles__terminating_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.manual_grade_for_no_whiles_terminating Imported.Original_LF__DOT__Imp_LF_Imp_manual__grade__for__no__whiles__terminating Original_LF__DOT__Imp_LF_Imp_manual__grade__for__no__whiles__terminating_iso := {}.