From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Isomorphisms.__0__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__repeat__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__Poly_LF_Poly_test__repeat1 : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Poly_LF_Poly_repeat (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0)))) (imported_S (imported_S imported_0)))
    (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0))))
       (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0)))) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat))) := Imported.Original_LF__DOT__Poly_LF_Poly_test__repeat1.
Instance Original_LF__DOT__Poly_LF_Poly_test__repeat1_iso : rel_iso
    (relax_Iso_Ts_Ps
       (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Poly_LF_Poly_repeat_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 1 0%nat imported_0 _0_iso)))) (S_iso (S_iso _0_iso)))
          (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 1 0%nat imported_0 _0_iso))))
             (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 1 0%nat imported_0 _0_iso)))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso)))))
    Original.LF_DOT_Poly.LF.Poly.test_repeat1 imported_Original_LF__DOT__Poly_LF_Poly_test__repeat1.
Proof.
  (* test_repeat1 is an admitted axiom in Original.v, so we need to prove the rel_iso *)
  (* rel_iso iso x y means: eq (to iso x) y *)
  unfold rel_iso.
  (* The goal is now: eq (to (relax_Iso...) test_repeat1) imported_test_repeat1 *)
  (* Since both sides are proofs of equality (props), and the target is SProp, 
     we can use proof irrelevance *)
  simpl.
  (* Both sides are proofs in SProp, so they are equal *)
  apply IsomorphismDefinitions.eq_refl.
Qed.
Instance: KnownConstant Original.LF_DOT_Poly.LF.Poly.test_repeat1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Poly_LF_Poly_test__repeat1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.test_repeat1 Original_LF__DOT__Poly_LF_Poly_test__repeat1_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.test_repeat1 Imported.Original_LF__DOT__Poly_LF_Poly_test__repeat1 Original_LF__DOT__Poly_LF_Poly_test__repeat1_iso := {}.