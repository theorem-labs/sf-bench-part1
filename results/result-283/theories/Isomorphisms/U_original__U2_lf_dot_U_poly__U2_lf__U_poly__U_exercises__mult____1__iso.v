From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
#[local] Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__mult__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__one__iso.

(* The imported mult_1 - using the correct type with cnat as the Type argument *)
Definition imported_Original_LF__DOT__Poly_LF_Poly_Exercises_mult__1 : 
  @imported_Corelib_Init_Logic_eq 
    Imported.Original_LF__DOT__Poly_LF_Poly_Exercises_cnat
    (imported_Original_LF__DOT__Poly_LF_Poly_Exercises_mult 
       imported_Original_LF__DOT__Poly_LF_Poly_Exercises_one
       imported_Original_LF__DOT__Poly_LF_Poly_Exercises_one)
    imported_Original_LF__DOT__Poly_LF_Poly_Exercises_one
  := Imported.Original_LF__DOT__Poly_LF_Poly_Exercises_mult__1.

(* Build Iso between Prop (=) and SProp (imported_eq) *)
Definition mult1_iso_type : Iso 
   (Original.LF_DOT_Poly.LF.Poly.Exercises.mult
      Original.LF_DOT_Poly.LF.Poly.Exercises.one
      Original.LF_DOT_Poly.LF.Poly.Exercises.one =
    Original.LF_DOT_Poly.LF.Poly.Exercises.one)
   (@imported_Corelib_Init_Logic_eq
      Imported.Original_LF__DOT__Poly_LF_Poly_Exercises_cnat
      (imported_Original_LF__DOT__Poly_LF_Poly_Exercises_mult
         imported_Original_LF__DOT__Poly_LF_Poly_Exercises_one
         imported_Original_LF__DOT__Poly_LF_Poly_Exercises_one)
      imported_Original_LF__DOT__Poly_LF_Poly_Exercises_one).
Proof.
  unshelve eapply Build_Iso.
  - (* to: Prop equality -> SProp equality *)
    intro; exact Imported.Original_LF__DOT__Poly_LF_Poly_Exercises_mult__1.
  - (* from: SProp equality -> Prop equality *)
    intro; exact Original.LF_DOT_Poly.LF.Poly.Exercises.mult_1.
  - (* to_from: SProp proof irrelevance *)
    intro; apply IsomorphismDefinitions.eq_refl.
  - (* from_to: Prop proof irrelevance via UIP *)
    intro h; apply seq_of_eq; apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

(* mult_1 is Admitted in the original, so this isomorphism is also admitted *)
(* This is allowed per the axiom list: Original.LF_DOT_Poly.LF.Poly.Exercises.mult_1 *)
Instance Original_LF__DOT__Poly_LF_Poly_Exercises_mult__1_iso : rel_iso mult1_iso_type
    Original.LF_DOT_Poly.LF.Poly.Exercises.mult_1 
    imported_Original_LF__DOT__Poly_LF_Poly_Exercises_mult__1.
Proof.
  unfold mult1_iso_type.
  simpl.
  apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_Poly.LF.Poly.Exercises.mult_1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Poly_LF_Poly_Exercises_mult__1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.Exercises.mult_1 Original_LF__DOT__Poly_LF_Poly_Exercises_mult__1_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.Exercises.mult_1 Imported.Original_LF__DOT__Poly_LF_Poly_Exercises_mult__1 Original_LF__DOT__Poly_LF_Poly_Exercises_mult__1_iso := {}.