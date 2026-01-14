From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_b__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_c__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_grade__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_gt__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_minus__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_plus__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__grade____comparison__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_test__grade__comparison4 : imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__Basics_LF_Basics_grade__comparison
       (imported_Original_LF__DOT__Basics_LF_Basics_Grade imported_Original_LF__DOT__Basics_LF_Basics_B imported_Original_LF__DOT__Basics_LF_Basics_Minus)
       (imported_Original_LF__DOT__Basics_LF_Basics_Grade imported_Original_LF__DOT__Basics_LF_Basics_C imported_Original_LF__DOT__Basics_LF_Basics_Plus))
    imported_Original_LF__DOT__Basics_LF_Basics_Gt := Imported.Original_LF__DOT__Basics_LF_Basics_test__grade__comparison4.
Instance Original_LF__DOT__Basics_LF_Basics_test__grade__comparison4_iso : rel_iso
    {|
      to :=
        Corelib_Init_Logic_eq_iso
          (Original_LF__DOT__Basics_LF_Basics_grade__comparison_iso
             (Original_LF__DOT__Basics_LF_Basics_Grade_iso Original_LF__DOT__Basics_LF_Basics_B_iso Original_LF__DOT__Basics_LF_Basics_Minus_iso)
             (Original_LF__DOT__Basics_LF_Basics_Grade_iso Original_LF__DOT__Basics_LF_Basics_C_iso Original_LF__DOT__Basics_LF_Basics_Plus_iso))
          Original_LF__DOT__Basics_LF_Basics_Gt_iso;
      from :=
        from
          (Corelib_Init_Logic_eq_iso
             (Original_LF__DOT__Basics_LF_Basics_grade__comparison_iso
                (Original_LF__DOT__Basics_LF_Basics_Grade_iso Original_LF__DOT__Basics_LF_Basics_B_iso Original_LF__DOT__Basics_LF_Basics_Minus_iso)
                (Original_LF__DOT__Basics_LF_Basics_Grade_iso Original_LF__DOT__Basics_LF_Basics_C_iso Original_LF__DOT__Basics_LF_Basics_Plus_iso))
             Original_LF__DOT__Basics_LF_Basics_Gt_iso);
      to_from :=
        fun
          x : imported_Corelib_Init_Logic_eq
                (imported_Original_LF__DOT__Basics_LF_Basics_grade__comparison
                   (imported_Original_LF__DOT__Basics_LF_Basics_Grade imported_Original_LF__DOT__Basics_LF_Basics_B imported_Original_LF__DOT__Basics_LF_Basics_Minus)
                   (imported_Original_LF__DOT__Basics_LF_Basics_Grade imported_Original_LF__DOT__Basics_LF_Basics_C imported_Original_LF__DOT__Basics_LF_Basics_Plus))
                imported_Original_LF__DOT__Basics_LF_Basics_Gt =>
        to_from
          (Corelib_Init_Logic_eq_iso
             (Original_LF__DOT__Basics_LF_Basics_grade__comparison_iso
                (Original_LF__DOT__Basics_LF_Basics_Grade_iso Original_LF__DOT__Basics_LF_Basics_B_iso Original_LF__DOT__Basics_LF_Basics_Minus_iso)
                (Original_LF__DOT__Basics_LF_Basics_Grade_iso Original_LF__DOT__Basics_LF_Basics_C_iso Original_LF__DOT__Basics_LF_Basics_Plus_iso))
             Original_LF__DOT__Basics_LF_Basics_Gt_iso)
          x;
      from_to :=
        fun
          x : Original.LF_DOT_Basics.LF.Basics.grade_comparison (Original.LF_DOT_Basics.LF.Basics.Grade Original.LF_DOT_Basics.LF.Basics.B Original.LF_DOT_Basics.LF.Basics.Minus)
                (Original.LF_DOT_Basics.LF.Basics.Grade Original.LF_DOT_Basics.LF.Basics.C Original.LF_DOT_Basics.LF.Basics.Plus) =
              Original.LF_DOT_Basics.LF.Basics.Gt =>
        seq_p_of_t
          (from_to
             (Corelib_Init_Logic_eq_iso
                (Original_LF__DOT__Basics_LF_Basics_grade__comparison_iso
                   (Original_LF__DOT__Basics_LF_Basics_Grade_iso Original_LF__DOT__Basics_LF_Basics_B_iso Original_LF__DOT__Basics_LF_Basics_Minus_iso)
                   (Original_LF__DOT__Basics_LF_Basics_Grade_iso Original_LF__DOT__Basics_LF_Basics_C_iso Original_LF__DOT__Basics_LF_Basics_Plus_iso))
                Original_LF__DOT__Basics_LF_Basics_Gt_iso)
             x)
    |} Original.LF_DOT_Basics.LF.Basics.test_grade_comparison4 imported_Original_LF__DOT__Basics_LF_Basics_test__grade__comparison4.
Proof.
  unfold rel_iso. simpl.
  apply IsomorphismDefinitions.eq_refl.
Qed.
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.test_grade_comparison4 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_test__grade__comparison4 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.test_grade_comparison4 Original_LF__DOT__Basics_LF_Basics_test__grade__comparison4_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.test_grade_comparison4 Imported.Original_LF__DOT__Basics_LF_Basics_test__grade__comparison4 Original_LF__DOT__Basics_LF_Basics_test__grade__comparison4_iso := {}.