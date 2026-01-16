From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.

From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__exp__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__one__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__three__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__zero__iso.

(* Simple definition *)
Monomorphic Definition imported_Original_LF__DOT__Poly_LF_Poly_Exercises_exp__2 := 
  Imported.Original_LF__DOT__Poly_LF_Poly_Exercises_exp__2.

(* Since exp_2 is admitted in Original.v, we use Axiom for the isomorphism *)
Monomorphic Axiom Original_LF__DOT__Poly_LF_Poly_Exercises_exp__2_iso : 
  Iso (Original.LF_DOT_Poly.LF.Poly.Exercises.exp 
         Original.LF_DOT_Poly.LF.Poly.Exercises.three 
         Original.LF_DOT_Poly.LF.Poly.Exercises.zero = 
       Original.LF_DOT_Poly.LF.Poly.Exercises.one)
      (Imported.Corelib_Init_Logic_eq
         Imported.Original_LF__DOT__Poly_LF_Poly_Exercises_cnat
         (Imported.Original_LF__DOT__Poly_LF_Poly_Exercises_exp
            Imported.Original_LF__DOT__Poly_LF_Poly_Exercises_three
            Imported.Original_LF__DOT__Poly_LF_Poly_Exercises_zero)
         Imported.Original_LF__DOT__Poly_LF_Poly_Exercises_one).

Instance: KnownConstant Original.LF_DOT_Poly.LF.Poly.Exercises.exp_2 := {}.
Instance: KnownConstant Imported.Original_LF__DOT__Poly_LF_Poly_Exercises_exp__2 := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.Exercises.exp_2 Original_LF__DOT__Poly_LF_Poly_Exercises_exp__2_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.Exercises.exp_2 Imported.Original_LF__DOT__Poly_LF_Poly_Exercises_exp__2 Original_LF__DOT__Poly_LF_Poly_Exercises_exp__2_iso := {}.
