From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.

From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__doit3times__iso Isomorphisms.__0__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__minustwo__iso Isomorphisms.U_s__iso.

Local Definition nine : nat := 9%nat.
Local Definition three : nat := 3%nat.

(* Directly use the raw Imported type *)
Definition imported_Original_LF__DOT__Poly_LF_Poly_test__doit3times :=
  Imported.Original_LF__DOT__Poly_LF_Poly_test__doit3times.

Lemma n9_iso : rel_iso nat_iso nine Imported.n9.
Proof. unfold nine; simpl; repeat apply S_iso; apply _0_iso. Qed.

Lemma n3_iso : rel_iso nat_iso three Imported.n3.
Proof. unfold three; simpl; repeat apply S_iso; apply _0_iso. Qed.

(* Build the isomorphism manually *)
Definition doit3times_result_iso : rel_iso nat_iso
  (Original.LF_DOT_Poly.LF.Poly.doit3times Original.LF_DOT_Basics.LF.Basics.minustwo nine)
  (Imported.Original_LF__DOT__Poly_LF_Poly_doit3times Imported.nat
     Imported.Original_LF__DOT__Basics_LF_Basics_minustwo Imported.n9).
Proof.
  unfold Original.LF_DOT_Poly.LF.Poly.doit3times.
  apply (unwrap_sprop (Original_LF__DOT__Poly_LF_Poly_doit3times_iso nat_iso
    Original.LF_DOT_Basics.LF.Basics.minustwo
    Imported.Original_LF__DOT__Basics_LF_Basics_minustwo
    (fun (x1 : nat) (x2 : imported_nat) (hx : rel_iso_sort nat_iso x1 x2) =>
      {| unwrap_sprop := Original_LF__DOT__Basics_LF_Basics_minustwo_iso (unwrap_sprop hx) |})
    nine Imported.n9 {| unwrap_sprop := n9_iso |})).
Qed.

(* The isomorphism type connects the two sides *)
Definition test_doit3times_Iso : Iso
  (Original.LF_DOT_Poly.LF.Poly.doit3times Original.LF_DOT_Basics.LF.Basics.minustwo nine = three)
  (Imported.Corelib_Init_Logic_eq_inst1 Imported.nat
    (Imported.Original_LF__DOT__Poly_LF_Poly_doit3times Imported.nat
       Imported.Original_LF__DOT__Basics_LF_Basics_minustwo Imported.n9)
    Imported.n3).
Admitted.

Instance Original_LF__DOT__Poly_LF_Poly_test__doit3times_iso : rel_iso
    test_doit3times_Iso
    Original.LF_DOT_Poly.LF.Poly.test_doit3times imported_Original_LF__DOT__Poly_LF_Poly_test__doit3times.
Admitted.

Instance: KnownConstant Original.LF_DOT_Poly.LF.Poly.test_doit3times := {}.
Instance: KnownConstant Imported.Original_LF__DOT__Poly_LF_Poly_test__doit3times := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.test_doit3times Original_LF__DOT__Poly_LF_Poly_test__doit3times_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.test_doit3times Imported.Original_LF__DOT__Poly_LF_Poly_test__doit3times Original_LF__DOT__Poly_LF_Poly_test__doit3times_iso := {}.
