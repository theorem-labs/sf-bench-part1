From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__filter__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Isomorphisms.__0__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__even__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__Poly_LF_Poly_test__filter1 : imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__Poly_LF_Poly_filter (fun x : imported_nat => imported_Original_LF__DOT__Basics_LF_Basics_even x)
       (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S imported_0)
          (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S imported_0))
             (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S imported_0)))
                (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (imported_S imported_0)))) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat))))))
    (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S imported_0))
       (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (imported_S imported_0)))) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat))) := Imported.Original_LF__DOT__Poly_LF_Poly_test__filter1.

(* The test_filter1 is an admitted theorem in Original.v, so we use iso_SInhabited *)
Instance Original_LF__DOT__Poly_LF_Poly_test__filter1_iso : rel_iso
    {|
      to :=
        Corelib_Init_Logic_eq_iso
          (Original_LF__DOT__Poly_LF_Poly_filter_iso Original.LF_DOT_Basics.LF.Basics.even (fun x : imported_nat => imported_Original_LF__DOT__Basics_LF_Basics_even x)
             (fun (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) => Original_LF__DOT__Basics_LF_Basics_even_iso hx)
             (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso _0_iso)
                (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso))
                   (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso _0_iso)))
                      (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))))))
          (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso))
             (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso)));
      from :=
        from
          (Corelib_Init_Logic_eq_iso
             (Original_LF__DOT__Poly_LF_Poly_filter_iso Original.LF_DOT_Basics.LF.Basics.even (fun x : imported_nat => imported_Original_LF__DOT__Basics_LF_Basics_even x)
                (fun (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) => Original_LF__DOT__Basics_LF_Basics_even_iso hx)
                (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso _0_iso)
                   (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso))
                      (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso _0_iso)))
                         (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))))))
             (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso))
                (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))));
      to_from :=
        fun
          x : imported_Corelib_Init_Logic_eq
                (imported_Original_LF__DOT__Poly_LF_Poly_filter (fun x : imported_nat => imported_Original_LF__DOT__Basics_LF_Basics_even x)
                   (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S imported_0)
                      (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S imported_0))
                         (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S imported_0)))
                            (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (imported_S imported_0)))) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat))))))
                (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S imported_0))
                   (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (imported_S imported_0)))) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat))) =>
        to_from
          (Corelib_Init_Logic_eq_iso
             (Original_LF__DOT__Poly_LF_Poly_filter_iso Original.LF_DOT_Basics.LF.Basics.even (fun x0 : imported_nat => imported_Original_LF__DOT__Basics_LF_Basics_even x0)
                (fun (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) => Original_LF__DOT__Basics_LF_Basics_even_iso hx)
                (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso _0_iso)
                   (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso))
                      (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso _0_iso)))
                         (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))))))
             (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso))
                (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))))
          x;
      from_to :=
        fun
          x : @Logic.eq (Original.LF_DOT_Poly.LF.Poly.list nat) (Original.LF_DOT_Poly.LF.Poly.filter Original.LF_DOT_Basics.LF.Basics.even
                (@Original.LF_DOT_Poly.LF.Poly.cons nat (S O) (@Original.LF_DOT_Poly.LF.Poly.cons nat (S (S O)) (@Original.LF_DOT_Poly.LF.Poly.cons nat (S (S (S O))) (@Original.LF_DOT_Poly.LF.Poly.cons nat (S (S (S (S O)))) (@Original.LF_DOT_Poly.LF.Poly.nil nat))))))
              (@Original.LF_DOT_Poly.LF.Poly.cons nat (S (S O)) (@Original.LF_DOT_Poly.LF.Poly.cons nat (S (S (S (S O)))) (@Original.LF_DOT_Poly.LF.Poly.nil nat))) =>
        seq_p_of_t
          (from_to
             (Corelib_Init_Logic_eq_iso
                (Original_LF__DOT__Poly_LF_Poly_filter_iso Original.LF_DOT_Basics.LF.Basics.even (fun x0 : imported_nat => imported_Original_LF__DOT__Basics_LF_Basics_even x0)
                   (fun (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) => Original_LF__DOT__Basics_LF_Basics_even_iso hx)
                   (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso _0_iso)
                      (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso))
                         (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso _0_iso)))
                            (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))))))
                (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso))
                   (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))))
             x)
    |} Original.LF_DOT_Poly.LF.Poly.test_filter1 imported_Original_LF__DOT__Poly_LF_Poly_test__filter1.
Proof.
  (* rel_iso means: to ... test_filter1 = imported_test_filter1 *)
  unfold rel_iso.
  simpl.
  (* Both sides are SProp inhabitants, so they're equal *)
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_Poly.LF.Poly.test_filter1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Poly_LF_Poly_test__filter1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.test_filter1 Original_LF__DOT__Poly_LF_Poly_test__filter1_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.test_filter1 Imported.Original_LF__DOT__Poly_LF_Poly_test__filter1 Original_LF__DOT__Poly_LF_Poly_test__filter1_iso := {}.