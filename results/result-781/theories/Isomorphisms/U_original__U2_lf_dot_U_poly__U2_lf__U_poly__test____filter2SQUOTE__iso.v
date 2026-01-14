From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
(* Don't import Lean to avoid Nat conflict *)
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__filter__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__length__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Isomorphisms.__0__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__eqb__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__Poly_LF_Poly_test__filter2' : imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__Poly_LF_Poly_filter
       (fun x : imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat => imported_Original_LF__DOT__Basics_LF_Basics_eqb (imported_Original_LF__DOT__Poly_LF_Poly_length x) (imported_S imported_0))
       (imported_Original_LF__DOT__Poly_LF_Poly_cons
          (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S imported_0)
             (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S imported_0)) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat)))
          (imported_Original_LF__DOT__Poly_LF_Poly_cons
             (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S imported_0))) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat))
             (imported_Original_LF__DOT__Poly_LF_Poly_cons
                (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (imported_S imported_0)))) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat))
                (imported_Original_LF__DOT__Poly_LF_Poly_cons
                   (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (imported_S (imported_S imported_0)))))
                      (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S imported_0))))))
                         (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S imported_0)))))))
                            (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat))))
                   (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat)
                      (imported_Original_LF__DOT__Poly_LF_Poly_cons
                         (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S imported_0))))))))
                            (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat))
                         (imported_Original_LF__DOT__Poly_LF_Poly_nil (imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat)))))))))
    (imported_Original_LF__DOT__Poly_LF_Poly_cons
       (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S imported_0))) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat))
       (imported_Original_LF__DOT__Poly_LF_Poly_cons
          (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (imported_S imported_0)))) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat))
          (imported_Original_LF__DOT__Poly_LF_Poly_cons
             (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S imported_0))))))))
                (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat))
             (imported_Original_LF__DOT__Poly_LF_Poly_nil (imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat))))) := Imported.Original_LF__DOT__Poly_LF_Poly_test__filter2'.
Instance Original_LF__DOT__Poly_LF_Poly_test__filter2'_iso : rel_iso
    {|
      to :=
        Corelib_Init_Logic_eq_iso
          (Original_LF__DOT__Poly_LF_Poly_filter_iso (fun l : Original.LF_DOT_Poly.LF.Poly.list nat => Original.LF_DOT_Basics.LF.Basics.eqb (Original.LF_DOT_Poly.LF.Poly.length l) 1)
             (fun x : imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat =>
              imported_Original_LF__DOT__Basics_LF_Basics_eqb (imported_Original_LF__DOT__Poly_LF_Poly_length x) (imported_S imported_0))
             (fun (x1 : Original.LF_DOT_Poly.LF.Poly.list nat) (x2 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat) (hx : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso nat_iso) x1 x2) =>
              Original_LF__DOT__Basics_LF_Basics_eqb_iso (Original_LF__DOT__Poly_LF_Poly_length_iso hx) (S_iso _0_iso))
             (Original_LF__DOT__Poly_LF_Poly_cons_iso
                (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso _0_iso) (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso)) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso)))
                (Original_LF__DOT__Poly_LF_Poly_cons_iso (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso _0_iso))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))
                   (Original_LF__DOT__Poly_LF_Poly_cons_iso (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))
                      (Original_LF__DOT__Poly_LF_Poly_cons_iso
                         (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))
                            (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))
                               (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))))
                         (Original_LF__DOT__Poly_LF_Poly_cons_iso (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso)
                            (Original_LF__DOT__Poly_LF_Poly_cons_iso
                               (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))
                               (Original_LF__DOT__Poly_LF_Poly_nil_iso (Original_LF__DOT__Poly_LF_Poly_list_iso nat_iso)))))))))
          (Original_LF__DOT__Poly_LF_Poly_cons_iso (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso _0_iso))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))
             (Original_LF__DOT__Poly_LF_Poly_cons_iso (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))
                (Original_LF__DOT__Poly_LF_Poly_cons_iso
                   (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))
                   (Original_LF__DOT__Poly_LF_Poly_nil_iso (Original_LF__DOT__Poly_LF_Poly_list_iso nat_iso)))));
      from :=
        from
          (Corelib_Init_Logic_eq_iso
             (Original_LF__DOT__Poly_LF_Poly_filter_iso (fun l : Original.LF_DOT_Poly.LF.Poly.list nat => Original.LF_DOT_Basics.LF.Basics.eqb (Original.LF_DOT_Poly.LF.Poly.length l) 1)
                (fun x : imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat =>
                 imported_Original_LF__DOT__Basics_LF_Basics_eqb (imported_Original_LF__DOT__Poly_LF_Poly_length x) (imported_S imported_0))
                (fun (x1 : Original.LF_DOT_Poly.LF.Poly.list nat) (x2 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat)
                   (hx : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso nat_iso) x1 x2) =>
                 Original_LF__DOT__Basics_LF_Basics_eqb_iso (Original_LF__DOT__Poly_LF_Poly_length_iso hx) (S_iso _0_iso))
                (Original_LF__DOT__Poly_LF_Poly_cons_iso
                   (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso _0_iso) (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso)) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso)))
                   (Original_LF__DOT__Poly_LF_Poly_cons_iso (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso _0_iso))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))
                      (Original_LF__DOT__Poly_LF_Poly_cons_iso (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))
                         (Original_LF__DOT__Poly_LF_Poly_cons_iso
                            (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))
                               (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))
                                  (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))))
                            (Original_LF__DOT__Poly_LF_Poly_cons_iso (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso)
                               (Original_LF__DOT__Poly_LF_Poly_cons_iso
                                  (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))
                                  (Original_LF__DOT__Poly_LF_Poly_nil_iso (Original_LF__DOT__Poly_LF_Poly_list_iso nat_iso)))))))))
             (Original_LF__DOT__Poly_LF_Poly_cons_iso (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso _0_iso))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))
                (Original_LF__DOT__Poly_LF_Poly_cons_iso (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))
                   (Original_LF__DOT__Poly_LF_Poly_cons_iso
                      (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))
                      (Original_LF__DOT__Poly_LF_Poly_nil_iso (Original_LF__DOT__Poly_LF_Poly_list_iso nat_iso))))));
      to_from :=
        fun
          x : imported_Corelib_Init_Logic_eq
                (imported_Original_LF__DOT__Poly_LF_Poly_filter
                   (fun x : imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat =>
                    imported_Original_LF__DOT__Basics_LF_Basics_eqb (imported_Original_LF__DOT__Poly_LF_Poly_length x) (imported_S imported_0))
                   (imported_Original_LF__DOT__Poly_LF_Poly_cons
                      (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S imported_0)
                         (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S imported_0)) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat)))
                      (imported_Original_LF__DOT__Poly_LF_Poly_cons
                         (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S imported_0))) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat))
                         (imported_Original_LF__DOT__Poly_LF_Poly_cons
                            (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (imported_S imported_0)))) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat))
                            (imported_Original_LF__DOT__Poly_LF_Poly_cons
                               (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (imported_S (imported_S imported_0)))))
                                  (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S imported_0))))))
                                     (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S imported_0)))))))
                                        (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat))))
                               (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat)
                                  (imported_Original_LF__DOT__Poly_LF_Poly_cons
                                     (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S imported_0))))))))
                                        (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat))
                                     (imported_Original_LF__DOT__Poly_LF_Poly_nil (imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat)))))))))
                (imported_Original_LF__DOT__Poly_LF_Poly_cons
                   (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S imported_0))) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat))
                   (imported_Original_LF__DOT__Poly_LF_Poly_cons
                      (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (imported_S imported_0)))) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat))
                      (imported_Original_LF__DOT__Poly_LF_Poly_cons
                         (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S imported_0))))))))
                            (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat))
                         (imported_Original_LF__DOT__Poly_LF_Poly_nil (imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat))))) =>
        to_from
          (Corelib_Init_Logic_eq_iso
             (Original_LF__DOT__Poly_LF_Poly_filter_iso (fun l : Original.LF_DOT_Poly.LF.Poly.list nat => Original.LF_DOT_Basics.LF.Basics.eqb (Original.LF_DOT_Poly.LF.Poly.length l) 1)
                (fun x0 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat =>
                 imported_Original_LF__DOT__Basics_LF_Basics_eqb (imported_Original_LF__DOT__Poly_LF_Poly_length x0) (imported_S imported_0))
                (fun (x1 : Original.LF_DOT_Poly.LF.Poly.list nat) (x2 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat)
                   (hx : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso nat_iso) x1 x2) =>
                 Original_LF__DOT__Basics_LF_Basics_eqb_iso (Original_LF__DOT__Poly_LF_Poly_length_iso hx) (S_iso _0_iso))
                (Original_LF__DOT__Poly_LF_Poly_cons_iso
                   (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso _0_iso) (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso)) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso)))
                   (Original_LF__DOT__Poly_LF_Poly_cons_iso (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso _0_iso))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))
                      (Original_LF__DOT__Poly_LF_Poly_cons_iso (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))
                         (Original_LF__DOT__Poly_LF_Poly_cons_iso
                            (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))
                               (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))
                                  (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))))
                            (Original_LF__DOT__Poly_LF_Poly_cons_iso (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso)
                               (Original_LF__DOT__Poly_LF_Poly_cons_iso
                                  (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))
                                  (Original_LF__DOT__Poly_LF_Poly_nil_iso (Original_LF__DOT__Poly_LF_Poly_list_iso nat_iso)))))))))
             (Original_LF__DOT__Poly_LF_Poly_cons_iso (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso _0_iso))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))
                (Original_LF__DOT__Poly_LF_Poly_cons_iso (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))
                   (Original_LF__DOT__Poly_LF_Poly_cons_iso
                      (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))
                      (Original_LF__DOT__Poly_LF_Poly_nil_iso (Original_LF__DOT__Poly_LF_Poly_list_iso nat_iso))))))
          x;
      from_to :=
        fun
          x : Original.LF_DOT_Poly.LF.Poly.filter (fun l : Original.LF_DOT_Poly.LF.Poly.list nat => Original.LF_DOT_Basics.LF.Basics.eqb (Original.LF_DOT_Poly.LF.Poly.length l) 1)
                (Original.LF_DOT_Poly.LF.Poly.cons (Original.LF_DOT_Poly.LF.Poly.cons 1 (Original.LF_DOT_Poly.LF.Poly.cons 2 Original.LF_DOT_Poly.LF.Poly.nil))
                   (Original.LF_DOT_Poly.LF.Poly.cons (Original.LF_DOT_Poly.LF.Poly.cons 3 Original.LF_DOT_Poly.LF.Poly.nil)
                      (Original.LF_DOT_Poly.LF.Poly.cons (Original.LF_DOT_Poly.LF.Poly.cons 4 Original.LF_DOT_Poly.LF.Poly.nil)
                         (Original.LF_DOT_Poly.LF.Poly.cons
                            (Original.LF_DOT_Poly.LF.Poly.cons 5 (Original.LF_DOT_Poly.LF.Poly.cons 6 (Original.LF_DOT_Poly.LF.Poly.cons 7 Original.LF_DOT_Poly.LF.Poly.nil)))
                            (Original.LF_DOT_Poly.LF.Poly.cons Original.LF_DOT_Poly.LF.Poly.nil
                               (Original.LF_DOT_Poly.LF.Poly.cons (Original.LF_DOT_Poly.LF.Poly.cons 8 Original.LF_DOT_Poly.LF.Poly.nil) Original.LF_DOT_Poly.LF.Poly.nil)))))) =
              Original.LF_DOT_Poly.LF.Poly.cons (Original.LF_DOT_Poly.LF.Poly.cons 3 Original.LF_DOT_Poly.LF.Poly.nil)
                (Original.LF_DOT_Poly.LF.Poly.cons (Original.LF_DOT_Poly.LF.Poly.cons 4 Original.LF_DOT_Poly.LF.Poly.nil)
                   (Original.LF_DOT_Poly.LF.Poly.cons (Original.LF_DOT_Poly.LF.Poly.cons 8 Original.LF_DOT_Poly.LF.Poly.nil) Original.LF_DOT_Poly.LF.Poly.nil)) =>
        seq_p_of_t
          (from_to
             (Corelib_Init_Logic_eq_iso
                (Original_LF__DOT__Poly_LF_Poly_filter_iso (fun l : Original.LF_DOT_Poly.LF.Poly.list nat => Original.LF_DOT_Basics.LF.Basics.eqb (Original.LF_DOT_Poly.LF.Poly.length l) 1)
                   (fun x0 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat =>
                    imported_Original_LF__DOT__Basics_LF_Basics_eqb (imported_Original_LF__DOT__Poly_LF_Poly_length x0) (imported_S imported_0))
                   (fun (x1 : Original.LF_DOT_Poly.LF.Poly.list nat) (x2 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat)
                      (hx : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso nat_iso) x1 x2) =>
                    Original_LF__DOT__Basics_LF_Basics_eqb_iso (Original_LF__DOT__Poly_LF_Poly_length_iso hx) (S_iso _0_iso))
                   (Original_LF__DOT__Poly_LF_Poly_cons_iso
                      (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso _0_iso) (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso)) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso)))
                      (Original_LF__DOT__Poly_LF_Poly_cons_iso (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso _0_iso))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))
                         (Original_LF__DOT__Poly_LF_Poly_cons_iso (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))
                            (Original_LF__DOT__Poly_LF_Poly_cons_iso
                               (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))
                                  (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))
                                     (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))))
                               (Original_LF__DOT__Poly_LF_Poly_cons_iso (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso)
                                  (Original_LF__DOT__Poly_LF_Poly_cons_iso
                                     (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))
                                     (Original_LF__DOT__Poly_LF_Poly_nil_iso (Original_LF__DOT__Poly_LF_Poly_list_iso nat_iso)))))))))
                (Original_LF__DOT__Poly_LF_Poly_cons_iso (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso _0_iso))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))
                   (Original_LF__DOT__Poly_LF_Poly_cons_iso (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))
                      (Original_LF__DOT__Poly_LF_Poly_cons_iso
                         (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))
                         (Original_LF__DOT__Poly_LF_Poly_nil_iso (Original_LF__DOT__Poly_LF_Poly_list_iso nat_iso))))))
             x)
    |} Original.LF_DOT_Poly.LF.Poly.test_filter2' imported_Original_LF__DOT__Poly_LF_Poly_test__filter2'.
Admitted.
Instance: KnownConstant Original.LF_DOT_Poly.LF.Poly.test_filter2' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Poly_LF_Poly_test__filter2' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.test_filter2' Original_LF__DOT__Poly_LF_Poly_test__filter2'_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.test_filter2' Imported.Original_LF__DOT__Poly_LF_Poly_test__filter2' Original_LF__DOT__Poly_LF_Poly_test__filter2'_iso := {}.