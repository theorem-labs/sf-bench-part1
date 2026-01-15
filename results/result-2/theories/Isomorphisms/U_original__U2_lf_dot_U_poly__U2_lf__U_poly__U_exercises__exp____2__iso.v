From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.

From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__exp__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__one__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__three__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__zero__iso.

(* exp_2 : exp three zero = one *)
(* Use the Lean import directly *)
Definition imported_Original_LF__DOT__Poly_LF_Poly_Exercises_exp__2 := 
  Imported.Original_LF__DOT__Poly_LF_Poly_Exercises_exp__2.

(* exp_2 is Admitted in Original.v - use axiom for isomorphism *)
Axiom Original_LF__DOT__Poly_LF_Poly_Exercises_exp__2_iso : 
  Iso (Original.LF_DOT_Poly.LF.Poly.Exercises.exp 
         Original.LF_DOT_Poly.LF.Poly.Exercises.three 
         Original.LF_DOT_Poly.LF.Poly.Exercises.zero = 
       Original.LF_DOT_Poly.LF.Poly.Exercises.one)
      (imported_Corelib_Init_Logic_eq
         (fun (x2 : Type) (x4 : x2 -> x2) (x6 : x2) =>
          @imported_Original_LF__DOT__Poly_LF_Poly_Exercises_exp 
            (fun (x : Type) (x0 : x -> x) (x1 : x) => @imported_Original_LF__DOT__Poly_LF_Poly_Exercises_three x (fun x3 : x => x0 x3) x1)
            (fun (x : Type) (x0 : x -> x) (x3 : x) => @imported_Original_LF__DOT__Poly_LF_Poly_Exercises_zero x (fun x1 : x => x0 x1) x3) 
            x2 (fun x : x2 => x4 x) x6)
         (fun (x2 : Type) (x4 : x2 -> x2) (x6 : x2) => @imported_Original_LF__DOT__Poly_LF_Poly_Exercises_one x2 (fun x : x2 => x4 x) x6)).

Instance: KnownConstant Original.LF_DOT_Poly.LF.Poly.Exercises.exp_2 := {}.
Instance: KnownConstant imported_Original_LF__DOT__Poly_LF_Poly_Exercises_exp__2 := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.Exercises.exp_2 Original_LF__DOT__Poly_LF_Poly_Exercises_exp__2_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.Exercises.exp_2 imported_Original_LF__DOT__Poly_LF_Poly_Exercises_exp__2 Original_LF__DOT__Poly_LF_Poly_Exercises_exp__2_iso := {}.
