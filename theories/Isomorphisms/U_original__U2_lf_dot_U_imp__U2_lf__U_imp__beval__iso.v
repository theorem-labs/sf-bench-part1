From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__bexp__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso Isomorphisms.bool__iso.

Monomorphic Definition imported_Original_LF__DOT__Imp_LF_Imp_beval : (imported_String_string -> imported_nat) -> imported_Original_LF__DOT__Imp_LF_Imp_bexp -> imported_bool := Imported.Original_LF__DOT__Imp_LF_Imp_beval.
Monomorphic Instance Original_LF__DOT__Imp_LF_Imp_beval_iso : forall (x1 : Original.LF_DOT_Imp.LF.Imp.state) (x2 : imported_String_string -> imported_nat),
  (forall (x3 : String.string) (x4 : imported_String_string), rel_iso String_string_iso x3 x4 -> rel_iso nat_iso (x1 x3) (x2 x4)) ->
  forall (x3 : Original.LF_DOT_Imp.LF.Imp.bexp) (x4 : imported_Original_LF__DOT__Imp_LF_Imp_bexp),
  rel_iso Original_LF__DOT__Imp_LF_Imp_bexp_iso x3 x4 -> rel_iso bool_iso (Original.LF_DOT_Imp.LF.Imp.beval x1 x3) (imported_Original_LF__DOT__Imp_LF_Imp_beval x2 x4).
Admitted.
Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.beval := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_beval := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.beval Original_LF__DOT__Imp_LF_Imp_beval_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.beval Imported.Original_LF__DOT__Imp_LF_Imp_beval Original_LF__DOT__Imp_LF_Imp_beval_iso := {}.