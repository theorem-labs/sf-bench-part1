From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__exp__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__plus__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__two__iso.

(* The imported exp__1 has the type expected by Interface *)
Definition imported_Original_LF__DOT__Poly_LF_Poly_Exercises_exp__1 : imported_Corelib_Init_Logic_eq
    (fun (x2 : Type) (x4 : x2 -> x2) (x6 : x2) =>
     imported_Original_LF__DOT__Poly_LF_Poly_Exercises_exp (fun (x : Type) (x0 : x -> x) (x1 : x) => imported_Original_LF__DOT__Poly_LF_Poly_Exercises_two (fun x3 : x => x0 x3) x1)
       (fun (x : Type) (x0 : x -> x) (x3 : x) => imported_Original_LF__DOT__Poly_LF_Poly_Exercises_two (fun x1 : x => x0 x1) x3) (fun x : x2 => x4 x) x6)
    (fun (x2 : Type) (x4 : x2 -> x2) (x6 : x2) =>
     imported_Original_LF__DOT__Poly_LF_Poly_Exercises_plus (fun (x : Type) (x0 : x -> x) (x1 : x) => imported_Original_LF__DOT__Poly_LF_Poly_Exercises_two (fun x3 : x => x0 x3) x1)
       (fun (x : Type) (x0 : x -> x) (x3 : x) => imported_Original_LF__DOT__Poly_LF_Poly_Exercises_two (fun x1 : x => x0 x1) x3) (fun x : x2 => x4 x) x6) 
  := Imported.Original_LF__DOT__Poly_LF_Poly_Exercises_exp__1.

(* Short aliases for the LHS and RHS cnat values *)
Local Definition orig_exp_two_two := Original.LF_DOT_Poly.LF.Poly.Exercises.exp Original.LF_DOT_Poly.LF.Poly.Exercises.two Original.LF_DOT_Poly.LF.Poly.Exercises.two.
Local Definition orig_plus_two_two := Original.LF_DOT_Poly.LF.Poly.Exercises.plus Original.LF_DOT_Poly.LF.Poly.Exercises.two Original.LF_DOT_Poly.LF.Poly.Exercises.two.

Local Definition imp_exp_two_two := 
  (fun (x2 : Type) (x4 : x2 -> x2) (x6 : x2) =>
     imported_Original_LF__DOT__Poly_LF_Poly_Exercises_exp 
       (fun (x : Type) (x0 : x -> x) (x1 : x) => imported_Original_LF__DOT__Poly_LF_Poly_Exercises_two (fun x3 : x => x0 x3) x1)
       (fun (x : Type) (x0 : x -> x) (x3 : x) => imported_Original_LF__DOT__Poly_LF_Poly_Exercises_two (fun x1 : x => x0 x1) x3) 
       (fun x : x2 => x4 x) x6).

Local Definition imp_plus_two_two := 
  (fun (x2 : Type) (x4 : x2 -> x2) (x6 : x2) =>
     imported_Original_LF__DOT__Poly_LF_Poly_Exercises_plus 
       (fun (x : Type) (x0 : x -> x) (x1 : x) => imported_Original_LF__DOT__Poly_LF_Poly_Exercises_two (fun x3 : x => x0 x3) x1)
       (fun (x : Type) (x0 : x -> x) (x3 : x) => imported_Original_LF__DOT__Poly_LF_Poly_Exercises_two (fun x1 : x => x0 x1) x3) 
       (fun x : x2 => x4 x) x6).

(* Build an Iso from Prop to SProp using proof irrelevance *)
Definition eq_iso : Iso (orig_exp_two_two = orig_plus_two_two)
                        (imported_Corelib_Init_Logic_eq imp_exp_two_two imp_plus_two_two).
Proof.
  unshelve eapply Build_Iso.
  - (* to: Prop -> SProp *)
    intro H.
    exact imported_Original_LF__DOT__Poly_LF_Poly_Exercises_exp__1.
  - (* from: SProp -> Prop *)
    intro H.
    exact Original.LF_DOT_Poly.LF.Poly.Exercises.exp_1.
  - (* to_from: in SProp, all proofs are equal *)
    intro. apply IsomorphismDefinitions.eq_refl.
  - (* from_to: in Prop, use proof irrelevance *)
    intro H.
    pose proof (Stdlib.Logic.ProofIrrelevance.proof_irrelevance _ H Original.LF_DOT_Poly.LF.Poly.Exercises.exp_1) as Hirr.
    rewrite Hirr.
    apply IsomorphismDefinitions.eq_refl.
Defined.

Instance Original_LF__DOT__Poly_LF_Poly_Exercises_exp__1_iso : rel_iso eq_iso Original.LF_DOT_Poly.LF.Poly.Exercises.exp_1 imported_Original_LF__DOT__Poly_LF_Poly_Exercises_exp__1.
Proof.
  unfold eq_iso.
  simpl.
  apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_Poly.LF.Poly.Exercises.exp_1 := {}. 
Instance: KnownConstant Imported.Original_LF__DOT__Poly_LF_Poly_Exercises_exp__1 := {}. 
Instance: IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.Exercises.exp_1 Original_LF__DOT__Poly_LF_Poly_Exercises_exp__1_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.Exercises.exp_1 Imported.Original_LF__DOT__Poly_LF_Poly_Exercises_exp__1 Original_LF__DOT__Poly_LF_Poly_Exercises_exp__1_iso := {}.
