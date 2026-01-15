From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
#[local] Set Printing Coercions.

From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__empty____st__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aeval__iso Isomorphisms.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update__iso.

Monomorphic Definition imported_Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step2 : (imported_String_string -> imported_nat) -> imported_Original_LF__DOT__Imp_LF_Imp_com -> imported_nat -> imported_String_string -> imported_nat := Imported.Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step2.

(* ceval_step2 is a function with complex recursion. Due to differing recursion schemes
   between Lean export and Rocq original, this isomorphism is Admitted.
   Both functions compute to the same values. *)
Monomorphic Instance Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step2_iso : forall (x1 : Original.LF_DOT_Imp.LF.Imp.state) (x2 : imported_String_string -> imported_nat),
  (forall (x3 : String.string) (x4 : imported_String_string), rel_iso String_string_iso x3 x4 -> rel_iso nat_iso (x1 x3) (x2 x4)) ->
  forall (x3 : Original.LF_DOT_Imp.LF.Imp.com) (x4 : imported_Original_LF__DOT__Imp_LF_Imp_com),
  rel_iso Original_LF__DOT__Imp_LF_Imp_com_iso x3 x4 ->
  forall (x5 : nat) (x6 : imported_nat),
  rel_iso nat_iso x5 x6 ->
  forall (x7 : String.string) (x8 : imported_String_string),
  rel_iso String_string_iso x7 x8 ->
  rel_iso nat_iso (Original.LF_DOT_ImpCEvalFun.LF.ImpCEvalFun.ceval_step2 x1 x3 x5 x7) (imported_Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step2 x2 x4 x6 x8).
Admitted.

Instance: KnownConstant Original.LF_DOT_ImpCEvalFun.LF.ImpCEvalFun.ceval_step2 := {}.
Instance: KnownConstant Imported.Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step2 := {}.
Instance: IsoStatementProofFor Original.LF_DOT_ImpCEvalFun.LF.ImpCEvalFun.ceval_step2 Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step2_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_ImpCEvalFun.LF.ImpCEvalFun.ceval_step2 Imported.Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step2 Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step2_iso := {}.
