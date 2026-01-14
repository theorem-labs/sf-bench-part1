From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_b0__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_b1__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_z__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__incr__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_test__bin__incr2 : imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__Basics_LF_Basics_incr (imported_Original_LF__DOT__Basics_LF_Basics_B0 (imported_Original_LF__DOT__Basics_LF_Basics_B1 imported_Original_LF__DOT__Basics_LF_Basics_Z)))
    (imported_Original_LF__DOT__Basics_LF_Basics_B1 (imported_Original_LF__DOT__Basics_LF_Basics_B1 imported_Original_LF__DOT__Basics_LF_Basics_Z)) := Imported.Original_LF__DOT__Basics_LF_Basics_test__bin__incr2.
(* Since test_bin_incr2 is an Admitted axiom in Original.v, we use an axiom for the isomorphism *)
Axiom Original_LF__DOT__Basics_LF_Basics_test__bin__incr2_iso : rel_iso
    {|
      to :=
        Corelib_Init_Logic_eq_iso
          (Original_LF__DOT__Basics_LF_Basics_incr_iso (Original_LF__DOT__Basics_LF_Basics_B0_iso (Original_LF__DOT__Basics_LF_Basics_B1_iso Original_LF__DOT__Basics_LF_Basics_Z_iso)))
          (Original_LF__DOT__Basics_LF_Basics_B1_iso (Original_LF__DOT__Basics_LF_Basics_B1_iso Original_LF__DOT__Basics_LF_Basics_Z_iso));
      from :=
        from
          (Corelib_Init_Logic_eq_iso
             (Original_LF__DOT__Basics_LF_Basics_incr_iso (Original_LF__DOT__Basics_LF_Basics_B0_iso (Original_LF__DOT__Basics_LF_Basics_B1_iso Original_LF__DOT__Basics_LF_Basics_Z_iso)))
             (Original_LF__DOT__Basics_LF_Basics_B1_iso (Original_LF__DOT__Basics_LF_Basics_B1_iso Original_LF__DOT__Basics_LF_Basics_Z_iso)));
      to_from :=
        fun
          x : imported_Corelib_Init_Logic_eq
                (imported_Original_LF__DOT__Basics_LF_Basics_incr
                   (imported_Original_LF__DOT__Basics_LF_Basics_B0 (imported_Original_LF__DOT__Basics_LF_Basics_B1 imported_Original_LF__DOT__Basics_LF_Basics_Z)))
                (imported_Original_LF__DOT__Basics_LF_Basics_B1 (imported_Original_LF__DOT__Basics_LF_Basics_B1 imported_Original_LF__DOT__Basics_LF_Basics_Z)) =>
        to_from
          (Corelib_Init_Logic_eq_iso
             (Original_LF__DOT__Basics_LF_Basics_incr_iso (Original_LF__DOT__Basics_LF_Basics_B0_iso (Original_LF__DOT__Basics_LF_Basics_B1_iso Original_LF__DOT__Basics_LF_Basics_Z_iso)))
             (Original_LF__DOT__Basics_LF_Basics_B1_iso (Original_LF__DOT__Basics_LF_Basics_B1_iso Original_LF__DOT__Basics_LF_Basics_Z_iso)))
          x;
      from_to :=
        fun
          x : Original.LF_DOT_Basics.LF.Basics.incr (Original.LF_DOT_Basics.LF.Basics.B0 (Original.LF_DOT_Basics.LF.Basics.B1 Original.LF_DOT_Basics.LF.Basics.Z)) =
              Original.LF_DOT_Basics.LF.Basics.B1 (Original.LF_DOT_Basics.LF.Basics.B1 Original.LF_DOT_Basics.LF.Basics.Z) =>
        seq_p_of_t
          (from_to
             (Corelib_Init_Logic_eq_iso
                (Original_LF__DOT__Basics_LF_Basics_incr_iso (Original_LF__DOT__Basics_LF_Basics_B0_iso (Original_LF__DOT__Basics_LF_Basics_B1_iso Original_LF__DOT__Basics_LF_Basics_Z_iso)))
                (Original_LF__DOT__Basics_LF_Basics_B1_iso (Original_LF__DOT__Basics_LF_Basics_B1_iso Original_LF__DOT__Basics_LF_Basics_Z_iso)))
             x)
    |} Original.LF_DOT_Basics.LF.Basics.test_bin_incr2 imported_Original_LF__DOT__Basics_LF_Basics_test__bin__incr2.
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.test_bin_incr2 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_test__bin__incr2 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.test_bin_incr2 Original_LF__DOT__Basics_LF_Basics_test__bin__incr2_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.test_bin_incr2 Imported.Original_LF__DOT__Basics_LF_Basics_test__bin__incr2 Original_LF__DOT__Basics_LF_Basics_test__bin__incr2_iso := {}.