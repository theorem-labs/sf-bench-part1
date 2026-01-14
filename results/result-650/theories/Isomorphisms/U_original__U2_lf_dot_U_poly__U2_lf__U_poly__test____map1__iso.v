From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__map__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Isomorphisms.__0__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__plus__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__Poly_LF_Poly_test__map1 : imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__Poly_LF_Poly_map (fun x : imported_nat => imported_Original_LF__DOT__Basics_LF_Basics_plus (imported_S (imported_S (imported_S imported_0))) x)
       (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S imported_0))
          (imported_Original_LF__DOT__Poly_LF_Poly_cons imported_0
             (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S imported_0)) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat)))))
    (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (imported_S (imported_S imported_0)))))
       (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S imported_0)))
          (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (imported_S (imported_S imported_0))))) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat)))) := Imported.Original_LF__DOT__Poly_LF_Poly_test__map1.
Instance Original_LF__DOT__Poly_LF_Poly_test__map1_iso : rel_iso
    {|
      to :=
        Corelib_Init_Logic_eq_iso
          (Original_LF__DOT__Poly_LF_Poly_map_iso (fun x : nat => Original.LF_DOT_Basics.LF.Basics.plus (3:nat) x)
             (fun x : imported_nat => imported_Original_LF__DOT__Basics_LF_Basics_plus (imported_S (imported_S (imported_S imported_0))) x)
             (fun (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) => Original_LF__DOT__Basics_LF_Basics_plus_iso (S_iso (S_iso (S_iso _0_iso))) hx)
             (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso))
                (Original_LF__DOT__Poly_LF_Poly_cons_iso _0_iso (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso)) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso)))))
          (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))
             (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso _0_iso)))
                (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))));
      from :=
        from
          (Corelib_Init_Logic_eq_iso
             (Original_LF__DOT__Poly_LF_Poly_map_iso (fun x : nat => Original.LF_DOT_Basics.LF.Basics.plus (3:nat) x)
                (fun x : imported_nat => imported_Original_LF__DOT__Basics_LF_Basics_plus (imported_S (imported_S (imported_S imported_0))) x)
                (fun (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) => Original_LF__DOT__Basics_LF_Basics_plus_iso (S_iso (S_iso (S_iso _0_iso))) hx)
                (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso))
                   (Original_LF__DOT__Poly_LF_Poly_cons_iso _0_iso (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso)) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso)))))
             (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))
                (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso _0_iso)))
                   (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso)))));
      to_from :=
        fun
          x : imported_Corelib_Init_Logic_eq
                (imported_Original_LF__DOT__Poly_LF_Poly_map (fun x : imported_nat => imported_Original_LF__DOT__Basics_LF_Basics_plus (imported_S (imported_S (imported_S imported_0))) x)
                   (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S imported_0))
                      (imported_Original_LF__DOT__Poly_LF_Poly_cons imported_0
                         (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S imported_0)) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat)))))
                (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (imported_S (imported_S imported_0)))))
                   (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S imported_0)))
                      (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (imported_S (imported_S imported_0)))))
                         (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat)))) =>
        to_from
          (Corelib_Init_Logic_eq_iso
             (Original_LF__DOT__Poly_LF_Poly_map_iso (fun x0 : nat => Original.LF_DOT_Basics.LF.Basics.plus 3 x0)
                (fun x0 : imported_nat => imported_Original_LF__DOT__Basics_LF_Basics_plus (imported_S (imported_S (imported_S imported_0))) x0)
                (fun (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) => Original_LF__DOT__Basics_LF_Basics_plus_iso (S_iso (S_iso (S_iso _0_iso))) hx)
                (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso))
                   (Original_LF__DOT__Poly_LF_Poly_cons_iso _0_iso (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso)) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso)))))
             (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))
                (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso _0_iso)))
                   (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso)))))
          x;
      from_to :=
        fun
          x : Original.LF_DOT_Poly.LF.Poly.map (fun x : nat => Original.LF_DOT_Basics.LF.Basics.plus (3:nat) x)
                (Original.LF_DOT_Poly.LF.Poly.cons (2:nat) (Original.LF_DOT_Poly.LF.Poly.cons (0:nat) (Original.LF_DOT_Poly.LF.Poly.cons (2:nat) Original.LF_DOT_Poly.LF.Poly.nil))) =
              Original.LF_DOT_Poly.LF.Poly.cons (5:nat) (Original.LF_DOT_Poly.LF.Poly.cons (3:nat) (Original.LF_DOT_Poly.LF.Poly.cons (5:nat) Original.LF_DOT_Poly.LF.Poly.nil)) =>
        seq_p_of_t
          (from_to
             (Corelib_Init_Logic_eq_iso
                (Original_LF__DOT__Poly_LF_Poly_map_iso (fun x0 : nat => Original.LF_DOT_Basics.LF.Basics.plus (3:nat) x0)
                   (fun x0 : imported_nat => imported_Original_LF__DOT__Basics_LF_Basics_plus (imported_S (imported_S (imported_S imported_0))) x0)
                   (fun (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) => Original_LF__DOT__Basics_LF_Basics_plus_iso (S_iso (S_iso (S_iso _0_iso))) hx)
                   (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso))
                      (Original_LF__DOT__Poly_LF_Poly_cons_iso _0_iso (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso)) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso)))))
                (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))
                   (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso _0_iso)))
                      (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso)))))
             x)
    |} Original.LF_DOT_Poly.LF.Poly.test_map1 imported_Original_LF__DOT__Poly_LF_Poly_test__map1.
Admitted.
Instance: KnownConstant Original.LF_DOT_Poly.LF.Poly.test_map1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Poly_LF_Poly_test__map1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.test_map1 Original_LF__DOT__Poly_LF_Poly_test__map1_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.test_map1 Imported.Original_LF__DOT__Poly_LF_Poly_test__map1 Original_LF__DOT__Poly_LF_Poly_test__map1_iso := {}.