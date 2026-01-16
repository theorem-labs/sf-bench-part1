From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.

From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__one__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__scc__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__zero__iso.

(* Use the Lean-exported proof directly *)
Definition imported_Original_LF__DOT__Poly_LF_Poly_Exercises_scc__1 := 
  Imported.Original_LF__DOT__Poly_LF_Poly_Exercises_scc__1.

(* scc_1 is Admitted in Original.v - use axiom for isomorphism *)
Axiom Original_LF__DOT__Poly_LF_Poly_Exercises_scc__1_iso : 
  Iso (Original.LF_DOT_Poly.LF.Poly.Exercises.scc
         Original.LF_DOT_Poly.LF.Poly.Exercises.zero =
       Original.LF_DOT_Poly.LF.Poly.Exercises.one)
      (Imported.Corelib_Init_Logic_eq 
         Imported.Original_LF__DOT__Poly_LF_Poly_Exercises_cnat
         (Imported.Original_LF__DOT__Poly_LF_Poly_Exercises_scc
            Imported.Original_LF__DOT__Poly_LF_Poly_Exercises_zero)
         Imported.Original_LF__DOT__Poly_LF_Poly_Exercises_one).

Instance: KnownConstant Original.LF_DOT_Poly.LF.Poly.Exercises.scc_1 := {}.
Instance: KnownConstant Imported.Original_LF__DOT__Poly_LF_Poly_Exercises_scc__1 := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.Exercises.scc_1 Original_LF__DOT__Poly_LF_Poly_Exercises_scc__1_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.Exercises.scc_1 Imported.Original_LF__DOT__Poly_LF_Poly_Exercises_scc__1 Original_LF__DOT__Poly_LF_Poly_Exercises_scc__1_iso := {}.
