From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__nostutter__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Isomorphisms.__0__iso Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__not__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_test__nostutter__4 : imported_Original_LF__DOT__IndProp_LF_IndProp_nostutter
    (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S imported_0)))
       (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S imported_0)
          (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S imported_0)
             (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0)))) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat))))) ->
  imported_Original_False.
Proof.
  (* imported_S is Imported.S = Lean.Nat_succ, imported_0 is Imported.O = Lean.Nat_zero *)
  (* We need to show this matches the type of Imported.Original_LF__DOT__IndProp_LF_IndProp_test__nostutter__4 *)
  unfold imported_S, imported_0.
  unfold imported_Original_LF__DOT__IndProp_LF_IndProp_nostutter, imported_Original_LF__DOT__Poly_LF_Poly_cons, imported_Original_LF__DOT__Poly_LF_Poly_nil, imported_Original_False, imported_nat.
  exact Imported.Original_LF__DOT__IndProp_LF_IndProp_test__nostutter__4.
Defined.
Instance Original_LF__DOT__IndProp_LF_IndProp_test__nostutter__4_iso : forall
    (x1 : Original.LF_DOT_IndProp.LF.IndProp.nostutter
            (Original.LF_DOT_Poly.LF.Poly.cons 3%nat (Original.LF_DOT_Poly.LF.Poly.cons 1%nat (Original.LF_DOT_Poly.LF.Poly.cons 1%nat (Original.LF_DOT_Poly.LF.Poly.cons (Datatypes.S (Datatypes.S (Datatypes.S (iterate1 Datatypes.S 1 0%nat)))) Original.LF_DOT_Poly.LF.Poly.nil)))))
    (x2 : imported_Original_LF__DOT__IndProp_LF_IndProp_nostutter
            (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S imported_0)))
               (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S imported_0)
                  (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S imported_0)
                     (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0)))) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat)))))),
  rel_iso
    (Original_LF__DOT__IndProp_LF_IndProp_nostutter_iso
       (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso _0_iso)))
          (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso _0_iso)
             (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso _0_iso)
                (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (iterate1D2 Datatypes.S imported_S S_iso 1 (Datatypes.O) imported_0 _0_iso)))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))))))
    x1 x2 ->
  rel_iso (relax_Iso_Ts_Ps Original_False_iso) (Original.LF_DOT_IndProp.LF.IndProp.test_nostutter_4 x1) (imported_Original_LF__DOT__IndProp_LF_IndProp_test__nostutter__4 x2).
Proof.
  (* Both x1 and x2 have type nostutter [...], which is an empty inductive type.
     So any statement about x1 or x2 can be proved by eliminating them. *)
  intros x1 x2 Hrel.
  (* x1 is of type nostutter [3;1;1;4] which is empty, use the SProp eliminator *)
  refine (Original.LF_DOT_IndProp.LF.IndProp.nostutter_sind Datatypes.nat (fun _ => _) _ x1).
Defined.
Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.test_nostutter_4 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_test__nostutter__4 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.test_nostutter_4 Original_LF__DOT__IndProp_LF_IndProp_test__nostutter__4_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.test_nostutter_4 Imported.Original_LF__DOT__IndProp_LF_IndProp_test__nostutter__4 Original_LF__DOT__IndProp_LF_IndProp_test__nostutter__4_iso := {}.