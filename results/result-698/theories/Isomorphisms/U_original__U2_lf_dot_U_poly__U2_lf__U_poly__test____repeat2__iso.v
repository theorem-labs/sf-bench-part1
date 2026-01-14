From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Isomorphisms.__0__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__repeat__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__Poly_LF_Poly_test__repeat2 : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Poly_LF_Poly_repeat imported_Original_LF__DOT__Basics_LF_Basics_false (imported_S imported_0))
    (imported_Original_LF__DOT__Poly_LF_Poly_cons imported_Original_LF__DOT__Basics_LF_Basics_false (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_Original_LF__DOT__Basics_LF_Basics_bool)) := Imported.Original_LF__DOT__Poly_LF_Poly_test__repeat2.
(* The isomorphism between two axioms - use iso_SInhabited since both are inhabited *)
Instance Original_LF__DOT__Poly_LF_Poly_test__repeat2_iso : rel_iso
    {|
      to :=
        Corelib_Init_Logic_eq_iso (Original_LF__DOT__Poly_LF_Poly_repeat_iso Original_LF__DOT__Basics_LF_Basics_false_iso (S_iso _0_iso))
          (Original_LF__DOT__Poly_LF_Poly_cons_iso Original_LF__DOT__Basics_LF_Basics_false_iso (Original_LF__DOT__Poly_LF_Poly_nil_iso Original_LF__DOT__Basics_LF_Basics_bool_iso));
      from :=
        from
          (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Poly_LF_Poly_repeat_iso Original_LF__DOT__Basics_LF_Basics_false_iso (S_iso _0_iso))
             (Original_LF__DOT__Poly_LF_Poly_cons_iso Original_LF__DOT__Basics_LF_Basics_false_iso (Original_LF__DOT__Poly_LF_Poly_nil_iso Original_LF__DOT__Basics_LF_Basics_bool_iso)));
      to_from :=
        fun
          x : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Poly_LF_Poly_repeat imported_Original_LF__DOT__Basics_LF_Basics_false (imported_S imported_0))
                (imported_Original_LF__DOT__Poly_LF_Poly_cons imported_Original_LF__DOT__Basics_LF_Basics_false
                   (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_Original_LF__DOT__Basics_LF_Basics_bool)) =>
        to_from
          (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Poly_LF_Poly_repeat_iso Original_LF__DOT__Basics_LF_Basics_false_iso (S_iso _0_iso))
             (Original_LF__DOT__Poly_LF_Poly_cons_iso Original_LF__DOT__Basics_LF_Basics_false_iso (Original_LF__DOT__Poly_LF_Poly_nil_iso Original_LF__DOT__Basics_LF_Basics_bool_iso)))
          x;
      from_to :=
        fun
          x : Original.LF_DOT_Poly.LF.Poly.repeat Original.LF_DOT_Basics.LF.Basics.bool Original.LF_DOT_Basics.LF.Basics.false 1 =
              Original.LF_DOT_Poly.LF.Poly.cons Original.LF_DOT_Basics.LF.Basics.false Original.LF_DOT_Poly.LF.Poly.nil =>
        seq_p_of_t
          (from_to
             (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Poly_LF_Poly_repeat_iso Original_LF__DOT__Basics_LF_Basics_false_iso (S_iso _0_iso))
                (Original_LF__DOT__Poly_LF_Poly_cons_iso Original_LF__DOT__Basics_LF_Basics_false_iso (Original_LF__DOT__Poly_LF_Poly_nil_iso Original_LF__DOT__Basics_LF_Basics_bool_iso)))
             x)
    |} Original.LF_DOT_Poly.LF.Poly.test_repeat2 imported_Original_LF__DOT__Poly_LF_Poly_test__repeat2.
Proof.
  unfold rel_iso.
  (* Both sides are proofs of equality in SProp, so they're equal *)
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_Poly.LF.Poly.test_repeat2 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Poly_LF_Poly_test__repeat2 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.test_repeat2 Original_LF__DOT__Poly_LF_Poly_test__repeat2_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.test_repeat2 Imported.Original_LF__DOT__Poly_LF_Poly_test__repeat2 Original_LF__DOT__Poly_LF_Poly_test__repeat2_iso := {}.