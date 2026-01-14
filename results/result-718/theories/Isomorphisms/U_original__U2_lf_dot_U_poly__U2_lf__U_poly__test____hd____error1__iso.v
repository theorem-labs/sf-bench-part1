From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_some__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__hd____error__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Isomorphisms.__0__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__Poly_LF_Poly_test__hd__error1 : imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__Poly_LF_Poly_hd__error
       (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S imported_0)
          (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S imported_0)) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat))))
    (imported_Original_LF__DOT__Poly_LF_Poly_Some (imported_S imported_0)) := Imported.Original_LF__DOT__Poly_LF_Poly_test__hd__error1.
Instance Original_LF__DOT__Poly_LF_Poly_test__hd__error1_iso : rel_iso
    {|
      to :=
        Corelib_Init_Logic_eq_iso
          (Original_LF__DOT__Poly_LF_Poly_hd__error_iso
             (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso _0_iso) (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso)) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))))
          (Original_LF__DOT__Poly_LF_Poly_Some_iso (S_iso _0_iso));
      from :=
        from
          (Corelib_Init_Logic_eq_iso
             (Original_LF__DOT__Poly_LF_Poly_hd__error_iso
                (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso _0_iso) (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso)) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))))
             (Original_LF__DOT__Poly_LF_Poly_Some_iso (S_iso _0_iso)));
      to_from :=
        fun
          x : imported_Corelib_Init_Logic_eq
                (imported_Original_LF__DOT__Poly_LF_Poly_hd__error
                   (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S imported_0)
                      (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S imported_0)) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat))))
                (imported_Original_LF__DOT__Poly_LF_Poly_Some (imported_S imported_0)) =>
        to_from
          (Corelib_Init_Logic_eq_iso
             (Original_LF__DOT__Poly_LF_Poly_hd__error_iso
                (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso _0_iso) (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso)) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))))
             (Original_LF__DOT__Poly_LF_Poly_Some_iso (S_iso _0_iso)))
          x;
      from_to :=
        fun
          x : Original.LF_DOT_Poly.LF.Poly.hd_error (Original.LF_DOT_Poly.LF.Poly.cons 1%nat (Original.LF_DOT_Poly.LF.Poly.cons 2%nat Original.LF_DOT_Poly.LF.Poly.nil)) = Original.LF_DOT_Poly.LF.Poly.Some 1%nat =>
        seq_p_of_t
          (from_to
             (Corelib_Init_Logic_eq_iso
                (Original_LF__DOT__Poly_LF_Poly_hd__error_iso
                   (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso _0_iso) (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso)) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))))
                (Original_LF__DOT__Poly_LF_Poly_Some_iso (S_iso _0_iso)))
             x)
    |} Original.LF_DOT_Poly.LF.Poly.test_hd_error1 imported_Original_LF__DOT__Poly_LF_Poly_test__hd__error1.
Admitted.
Instance: KnownConstant Original.LF_DOT_Poly.LF.Poly.test_hd_error1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Poly_LF_Poly_test__hd__error1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.test_hd_error1 Original_LF__DOT__Poly_LF_Poly_test__hd__error1_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.test_hd_error1 Imported.Original_LF__DOT__Poly_LF_Poly_test__hd__error1 Original_LF__DOT__Poly_LF_Poly_test__hd__error1_iso := {}.