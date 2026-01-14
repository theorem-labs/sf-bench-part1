From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__com__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__result__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso.

Definition imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval : imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_com ->
  (imported_String_string -> imported_nat) -> imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_result -> (imported_String_string -> imported_nat) -> SProp := Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval.
Instance Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval_iso : (forall (x1 : Original.LF_DOT_Imp.LF.Imp.BreakImp.com) (x2 : imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_com)
     (_ : @rel_iso Original.LF_DOT_Imp.LF.Imp.BreakImp.com imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_com Original_LF__DOT__Imp_LF_Imp_BreakImp_com_iso x1 x2)
     (x3 : Original.LF_DOT_Imp.LF.Imp.state) (x4 : forall _ : imported_String_string, imported_nat)
     (_ : forall (x5 : String.string) (x6 : imported_String_string) (_ : @rel_iso String.string imported_String_string String_string_iso x5 x6), @rel_iso nat imported_nat nat_iso (x3 x5) (x4 x6))
     (x5 : Original.LF_DOT_Imp.LF.Imp.BreakImp.result) (x6 : imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_result)
     (_ : @rel_iso Original.LF_DOT_Imp.LF.Imp.BreakImp.result imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_result Original_LF__DOT__Imp_LF_Imp_BreakImp_result_iso x5 x6)
     (x7 : Original.LF_DOT_Imp.LF.Imp.state) (x8 : forall _ : imported_String_string, imported_nat)
     (_ : forall (x9 : String.string) (x10 : imported_String_string) (_ : @rel_iso String.string imported_String_string String_string_iso x9 x10), @rel_iso nat imported_nat nat_iso (x7 x9) (x8 x10)),
   Iso (Original.LF_DOT_Imp.LF.Imp.BreakImp.ceval x1 x3 x5 x7) (imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval x2 x4 x6 x8)).
Proof.
  intros.
  (* ceval is an SProp-valued relation; we can always build an Iso using proof irrelevance *)
  refine (Build_Iso (fun _ => Imported._inhabitedExprDummy) (fun _ => _inhabitedExprDummy) _ _).
  - intro q. apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
  - intro p. apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.
Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.BreakImp.ceval := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.BreakImp.ceval Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.BreakImp.ceval Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval_iso := {}.