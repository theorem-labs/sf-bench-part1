From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__plus3__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__Poly_LF_Poly_test__plus3 : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Poly_LF_Poly_plus3 (imported_S (imported_S (imported_S (imported_S imported_0)))))
    (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S imported_0))))))) := Imported.Original_LF__DOT__Poly_LF_Poly_test__plus3.

(* The isomorphism is between two SProp types, both inhabited. We use proof irrelevance. *)
Definition the_iso := Corelib_Init_Logic_eq_iso (Original_LF__DOT__Poly_LF_Poly_plus3_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))) (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))).

Instance Original_LF__DOT__Poly_LF_Poly_test__plus3_iso : rel_iso
    {|
      to := the_iso;
      from := from the_iso;
      to_from := fun x => to_from the_iso x;
      from_to := fun x => seq_p_of_t (from_to the_iso x)
    |} Original.LF_DOT_Poly.LF.Poly.test_plus3 imported_Original_LF__DOT__Poly_LF_Poly_test__plus3.
Proof.
  unfold rel_iso, the_iso. simpl.
  (* Both test_plus3 (original) and imported are proofs of the same equality,
     so both get mapped to Corelib_Init_Logic_eq_refl after going through the iso *)
  (* The original statement is: plus3 4 = 7, i.e., 7 = 7 *)
  (* The imported statement is Corelib_Init_Logic_eq 7 7 in imported nat *)
  (* We need to show that to(test_plus3) = imported_test_plus3 in SProp *)
  (* Since this is SProp equality, any two proofs are equal *)
  apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_Poly.LF.Poly.test_plus3 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Poly_LF_Poly_test__plus3 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.test_plus3 Original_LF__DOT__Poly_LF_Poly_test__plus3_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.test_plus3 Imported.Original_LF__DOT__Poly_LF_Poly_test__plus3 Original_LF__DOT__Poly_LF_Poly_test__plus3_iso := {}.