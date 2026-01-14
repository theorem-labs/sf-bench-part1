From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_b0__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_b1__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_z__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__incr__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_test__bin__incr3 : imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__Basics_LF_Basics_incr (imported_Original_LF__DOT__Basics_LF_Basics_B1 (imported_Original_LF__DOT__Basics_LF_Basics_B1 imported_Original_LF__DOT__Basics_LF_Basics_Z)))
    (imported_Original_LF__DOT__Basics_LF_Basics_B0 (imported_Original_LF__DOT__Basics_LF_Basics_B0 (imported_Original_LF__DOT__Basics_LF_Basics_B1 imported_Original_LF__DOT__Basics_LF_Basics_Z))) := Imported.Original_LF__DOT__Basics_LF_Basics_test__bin__incr3.
Instance Original_LF__DOT__Basics_LF_Basics_test__bin__incr3_iso : rel_iso
    {|
      to :=
        Corelib_Init_Logic_eq_iso
          (Original_LF__DOT__Basics_LF_Basics_incr_iso (Original_LF__DOT__Basics_LF_Basics_B1_iso (Original_LF__DOT__Basics_LF_Basics_B1_iso Original_LF__DOT__Basics_LF_Basics_Z_iso)))
          (Original_LF__DOT__Basics_LF_Basics_B0_iso (Original_LF__DOT__Basics_LF_Basics_B0_iso (Original_LF__DOT__Basics_LF_Basics_B1_iso Original_LF__DOT__Basics_LF_Basics_Z_iso)));
      from :=
        from
          (Corelib_Init_Logic_eq_iso
             (Original_LF__DOT__Basics_LF_Basics_incr_iso (Original_LF__DOT__Basics_LF_Basics_B1_iso (Original_LF__DOT__Basics_LF_Basics_B1_iso Original_LF__DOT__Basics_LF_Basics_Z_iso)))
             (Original_LF__DOT__Basics_LF_Basics_B0_iso (Original_LF__DOT__Basics_LF_Basics_B0_iso (Original_LF__DOT__Basics_LF_Basics_B1_iso Original_LF__DOT__Basics_LF_Basics_Z_iso))));
      to_from :=
        fun
          x : imported_Corelib_Init_Logic_eq
                (imported_Original_LF__DOT__Basics_LF_Basics_incr
                   (imported_Original_LF__DOT__Basics_LF_Basics_B1 (imported_Original_LF__DOT__Basics_LF_Basics_B1 imported_Original_LF__DOT__Basics_LF_Basics_Z)))
                (imported_Original_LF__DOT__Basics_LF_Basics_B0
                   (imported_Original_LF__DOT__Basics_LF_Basics_B0 (imported_Original_LF__DOT__Basics_LF_Basics_B1 imported_Original_LF__DOT__Basics_LF_Basics_Z))) =>
        to_from
          (Corelib_Init_Logic_eq_iso
             (Original_LF__DOT__Basics_LF_Basics_incr_iso (Original_LF__DOT__Basics_LF_Basics_B1_iso (Original_LF__DOT__Basics_LF_Basics_B1_iso Original_LF__DOT__Basics_LF_Basics_Z_iso)))
             (Original_LF__DOT__Basics_LF_Basics_B0_iso (Original_LF__DOT__Basics_LF_Basics_B0_iso (Original_LF__DOT__Basics_LF_Basics_B1_iso Original_LF__DOT__Basics_LF_Basics_Z_iso))))
          x;
      from_to :=
        fun
          x : Original.LF_DOT_Basics.LF.Basics.incr (Original.LF_DOT_Basics.LF.Basics.B1 (Original.LF_DOT_Basics.LF.Basics.B1 Original.LF_DOT_Basics.LF.Basics.Z)) =
              Original.LF_DOT_Basics.LF.Basics.B0 (Original.LF_DOT_Basics.LF.Basics.B0 (Original.LF_DOT_Basics.LF.Basics.B1 Original.LF_DOT_Basics.LF.Basics.Z)) =>
        seq_p_of_t
          (from_to
             (Corelib_Init_Logic_eq_iso
                (Original_LF__DOT__Basics_LF_Basics_incr_iso (Original_LF__DOT__Basics_LF_Basics_B1_iso (Original_LF__DOT__Basics_LF_Basics_B1_iso Original_LF__DOT__Basics_LF_Basics_Z_iso)))
                (Original_LF__DOT__Basics_LF_Basics_B0_iso (Original_LF__DOT__Basics_LF_Basics_B0_iso (Original_LF__DOT__Basics_LF_Basics_B1_iso Original_LF__DOT__Basics_LF_Basics_Z_iso))))
             x)
    |} Original.LF_DOT_Basics.LF.Basics.test_bin_incr3 imported_Original_LF__DOT__Basics_LF_Basics_test__bin__incr3.
Proof.
  unfold rel_iso. simpl.
  unfold imported_Original_LF__DOT__Basics_LF_Basics_test__bin__incr3.
  unfold imported_Corelib_Init_Logic_eq.
  unfold imported_Original_LF__DOT__Basics_LF_Basics_incr.
  unfold imported_Original_LF__DOT__Basics_LF_Basics_B0.
  unfold imported_Original_LF__DOT__Basics_LF_Basics_B1.
  unfold imported_Original_LF__DOT__Basics_LF_Basics_Z.
  (* The goal should now be about showing that the to of the isomorphism applied to test_bin_incr3 equals the imported axiom *)
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.test_bin_incr3 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_test__bin__incr3 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.test_bin_incr3 Original_LF__DOT__Basics_LF_Basics_test__bin__incr3_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.test_bin_incr3 Imported.Original_LF__DOT__Basics_LF_Basics_test__bin__incr3 Original_LF__DOT__Basics_LF_Basics_test__bin__incr3_iso := {}.