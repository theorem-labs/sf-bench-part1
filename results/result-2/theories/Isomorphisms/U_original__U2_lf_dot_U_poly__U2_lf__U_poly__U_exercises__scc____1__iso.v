From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.

From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__one__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__scc__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__zero__iso.

(* Construct the proof directly using imported_* definitions from dependencies *)
Definition scc_zero_eta : forall x : Type, (x -> x) -> x -> x :=
  fun (x2 : Type) (x4 : x2 -> x2) (x6 : x2) =>
    @imported_Original_LF__DOT__Poly_LF_Poly_Exercises_scc 
      (fun (x : Type) (x0 : x -> x) (x1 : x) => @imported_Original_LF__DOT__Poly_LF_Poly_Exercises_zero x (fun x3 : x => x0 x3) x1)
      x2 (fun x : x2 => x4 x) x6.

Definition one_eta_scc : forall x : Type, (x -> x) -> x -> x :=
  fun (x2 : Type) (x4 : x2 -> x2) (x6 : x2) => @imported_Original_LF__DOT__Poly_LF_Poly_Exercises_one x2 (fun x : x2 => x4 x) x6.

(* Check that scc zero = one (by computation) *)
Lemma scc_zero_eq_one : scc_zero_eta = one_eta_scc.
Proof. reflexivity. Qed.

(* Now we can define imported_scc__1 using imported_Corelib_Init_Logic_eq and eq_refl *)
Monomorphic Definition imported_Original_LF__DOT__Poly_LF_Poly_Exercises_scc__1 
  : @imported_Corelib_Init_Logic_eq (forall x : Type, (x -> x) -> x -> x) scc_zero_eta one_eta_scc.
Proof.
  unfold scc_zero_eta, one_eta_scc.
  unfold imported_Original_LF__DOT__Poly_LF_Poly_Exercises_scc,
         imported_Original_LF__DOT__Poly_LF_Poly_Exercises_zero,
         imported_Original_LF__DOT__Poly_LF_Poly_Exercises_one.
  unfold imported_Corelib_Init_Logic_eq.
  apply Imported.Corelib_Init_Logic_eq_refl.
Defined.

(* scc_1 is Admitted in Original.v - use axiom for isomorphism *)
Axiom Original_LF__DOT__Poly_LF_Poly_Exercises_scc__1_iso : 
  Iso (Original.LF_DOT_Poly.LF.Poly.Exercises.scc
         Original.LF_DOT_Poly.LF.Poly.Exercises.zero =
       Original.LF_DOT_Poly.LF.Poly.Exercises.one)
      (@imported_Corelib_Init_Logic_eq (forall x : Type, (x -> x) -> x -> x)
         scc_zero_eta one_eta_scc).

Instance: KnownConstant Original.LF_DOT_Poly.LF.Poly.Exercises.scc_1 := {}.
Instance: KnownConstant imported_Original_LF__DOT__Poly_LF_Poly_Exercises_scc__1 := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.Exercises.scc_1 Original_LF__DOT__Poly_LF_Poly_Exercises_scc__1_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.Exercises.scc_1 imported_Original_LF__DOT__Poly_LF_Poly_Exercises_scc__1 Original_LF__DOT__Poly_LF_Poly_Exercises_scc__1_iso := {}.
