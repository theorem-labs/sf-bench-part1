From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__rev__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.

Definition imported_Original_LF__DOT__Poly_LF_Poly_test__rev2 := Imported.Original_LF__DOT__Poly_LF_Poly_test__rev2.

Instance Original_LF__DOT__Poly_LF_Poly_test__rev2_iso : rel_iso
    (relax_Iso_Ts_Ps
       (Corelib_Init_Logic_eq_iso
          (Original_LF__DOT__Poly_LF_Poly_rev_iso
             (Original_LF__DOT__Poly_LF_Poly_cons_iso Original_LF__DOT__Basics_LF_Basics_true_iso (Original_LF__DOT__Poly_LF_Poly_nil_iso Original_LF__DOT__Basics_LF_Basics_bool_iso)))
          (Original_LF__DOT__Poly_LF_Poly_cons_iso Original_LF__DOT__Basics_LF_Basics_true_iso (Original_LF__DOT__Poly_LF_Poly_nil_iso Original_LF__DOT__Basics_LF_Basics_bool_iso))))
    Original.LF_DOT_Poly.LF.Poly.test_rev2 imported_Original_LF__DOT__Poly_LF_Poly_test__rev2.
Proof.
  (* The original test_rev2 is Admitted, so we can use the axiom to relate it to the imported version *)
  unfold rel_iso.
  unfold relax_Iso_Ts_Ps. simpl.
  (* Since both sides are proofs of propositions in SProp, they are definitionally equal *)
  apply IsomorphismDefinitions.eq_refl.
Qed.
Instance: KnownConstant Original.LF_DOT_Poly.LF.Poly.test_rev2 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Poly_LF_Poly_test__rev2 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.test_rev2 Original_LF__DOT__Poly_LF_Poly_test__rev2_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.test_rev2 Imported.Original_LF__DOT__Poly_LF_Poly_test__rev2 Original_LF__DOT__Poly_LF_Poly_test__rev2_iso := {}.