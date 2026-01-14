From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__map__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Isomorphisms.__0__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__even__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__odd__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__Poly_LF_Poly_test__map3 := Imported.Original_LF__DOT__Poly_LF_Poly_test__map3.

(* This corresponds to an Admitted theorem in Original.v, so we use Admitted here *)
Instance Original_LF__DOT__Poly_LF_Poly_test__map3_iso : rel_iso
    (Corelib_Init_Logic_eq_iso
       (Original_LF__DOT__Poly_LF_Poly_map_iso
          (fun n : nat =>
           Original.LF_DOT_Poly.LF.Poly.cons (Original.LF_DOT_Basics.LF.Basics.even n) (Original.LF_DOT_Poly.LF.Poly.cons (Original.LF_DOT_Basics.LF.Basics.odd n) Original.LF_DOT_Poly.LF.Poly.nil))
          (fun x : imported_nat =>
           imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_Original_LF__DOT__Basics_LF_Basics_even x)
             (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_Original_LF__DOT__Basics_LF_Basics_odd x)
                (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_Original_LF__DOT__Basics_LF_Basics_bool)))
          (fun (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) =>
           Original_LF__DOT__Poly_LF_Poly_cons_iso (Original_LF__DOT__Basics_LF_Basics_even_iso hx)
             (Original_LF__DOT__Poly_LF_Poly_cons_iso (Original_LF__DOT__Basics_LF_Basics_odd_iso hx) (Original_LF__DOT__Poly_LF_Poly_nil_iso Original_LF__DOT__Basics_LF_Basics_bool_iso)))
          (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso))
             (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso _0_iso)
                (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso))
                   (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))))))
       (Original_LF__DOT__Poly_LF_Poly_cons_iso
          (Original_LF__DOT__Poly_LF_Poly_cons_iso Original_LF__DOT__Basics_LF_Basics_true_iso
             (Original_LF__DOT__Poly_LF_Poly_cons_iso Original_LF__DOT__Basics_LF_Basics_false_iso (Original_LF__DOT__Poly_LF_Poly_nil_iso Original_LF__DOT__Basics_LF_Basics_bool_iso)))
          (Original_LF__DOT__Poly_LF_Poly_cons_iso
             (Original_LF__DOT__Poly_LF_Poly_cons_iso Original_LF__DOT__Basics_LF_Basics_false_iso
                (Original_LF__DOT__Poly_LF_Poly_cons_iso Original_LF__DOT__Basics_LF_Basics_true_iso (Original_LF__DOT__Poly_LF_Poly_nil_iso Original_LF__DOT__Basics_LF_Basics_bool_iso)))
             (Original_LF__DOT__Poly_LF_Poly_cons_iso
                (Original_LF__DOT__Poly_LF_Poly_cons_iso Original_LF__DOT__Basics_LF_Basics_true_iso
                   (Original_LF__DOT__Poly_LF_Poly_cons_iso Original_LF__DOT__Basics_LF_Basics_false_iso (Original_LF__DOT__Poly_LF_Poly_nil_iso Original_LF__DOT__Basics_LF_Basics_bool_iso)))
                (Original_LF__DOT__Poly_LF_Poly_cons_iso
                   (Original_LF__DOT__Poly_LF_Poly_cons_iso Original_LF__DOT__Basics_LF_Basics_false_iso
                      (Original_LF__DOT__Poly_LF_Poly_cons_iso Original_LF__DOT__Basics_LF_Basics_true_iso (Original_LF__DOT__Poly_LF_Poly_nil_iso Original_LF__DOT__Basics_LF_Basics_bool_iso)))
                   (Original_LF__DOT__Poly_LF_Poly_nil_iso (Original_LF__DOT__Poly_LF_Poly_list_iso Original_LF__DOT__Basics_LF_Basics_bool_iso)))))))
    Original.LF_DOT_Poly.LF.Poly.test_map3 
    imported_Original_LF__DOT__Poly_LF_Poly_test__map3.
Proof.
  unfold rel_iso, imported_Original_LF__DOT__Poly_LF_Poly_test__map3.
  (* Both are in SProp, so we use proof irrelevance *)
  apply IsomorphismDefinitions.eq_refl.
Qed.

Instance: KnownConstant Original.LF_DOT_Poly.LF.Poly.test_map3 := {}.
Instance: KnownConstant Imported.Original_LF__DOT__Poly_LF_Poly_test__map3 := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.test_map3 Original_LF__DOT__Poly_LF_Poly_test__map3_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.test_map3 Imported.Original_LF__DOT__Poly_LF_Poly_test__map3 Original_LF__DOT__Poly_LF_Poly_test__map3_iso := {}.
