From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__fold____length__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Isomorphisms.__0__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__Poly_LF_Poly_Exercises_test__fold__length1 : imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length
       (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (imported_S imported_0))))
          (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S imported_0)))))))
             (imported_Original_LF__DOT__Poly_LF_Poly_cons imported_0 (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat)))))
    (imported_S (imported_S (imported_S imported_0))) := Imported.Original_LF__DOT__Poly_LF_Poly_Exercises_test__fold__length1.

(* Build the eq_iso instance for our specific types *)
Definition eq_iso_instance := 
  Corelib_Init_Logic_eq_iso
    (Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length_iso
       (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))
          (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))))
             (Original_LF__DOT__Poly_LF_Poly_cons_iso _0_iso (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso)))))
    (S_iso (S_iso (S_iso _0_iso))).

(* The original test_fold_length1 is Admitted, so this is an axiom isomorphism *)
(* Both sides are in SProp, so they're equal by proof irrelevance *)
Instance Original_LF__DOT__Poly_LF_Poly_Exercises_test__fold__length1_iso : rel_iso
    eq_iso_instance
    Original.LF_DOT_Poly.LF.Poly.Exercises.test_fold_length1 
    imported_Original_LF__DOT__Poly_LF_Poly_Exercises_test__fold__length1.
Proof.
  unfold rel_iso.
  simpl.
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_Poly.LF.Poly.Exercises.test_fold_length1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Poly_LF_Poly_Exercises_test__fold__length1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.Exercises.test_fold_length1 Original_LF__DOT__Poly_LF_Poly_Exercises_test__fold__length1_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.Exercises.test_fold_length1 Imported.Original_LF__DOT__Poly_LF_Poly_Exercises_test__fold__length1 Original_LF__DOT__Poly_LF_Poly_Exercises_test__fold__length1_iso := {}.