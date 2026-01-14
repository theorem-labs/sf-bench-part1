From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__nandb__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_test__nandb2 : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_nandb imported_Original_LF__DOT__Basics_LF_Basics_false imported_Original_LF__DOT__Basics_LF_Basics_false)
    imported_Original_LF__DOT__Basics_LF_Basics_true := Imported.Original_LF__DOT__Basics_LF_Basics_test__nandb2.

(* The test_nandb2 isomorphism is axiomatic because test_nandb2 is admitted in Original.v *)
(* Both test_nandb2 axioms state that nandb false false = true *)
Axiom Original_LF__DOT__Basics_LF_Basics_test__nandb2_iso : rel_iso
    {|
      to :=
        Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_nandb_iso Original_LF__DOT__Basics_LF_Basics_false_iso Original_LF__DOT__Basics_LF_Basics_false_iso)
          Original_LF__DOT__Basics_LF_Basics_true_iso;
      from :=
        from
          (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_nandb_iso Original_LF__DOT__Basics_LF_Basics_false_iso Original_LF__DOT__Basics_LF_Basics_false_iso)
             Original_LF__DOT__Basics_LF_Basics_true_iso);
      to_from :=
        fun
          x : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_nandb imported_Original_LF__DOT__Basics_LF_Basics_false imported_Original_LF__DOT__Basics_LF_Basics_false)
                imported_Original_LF__DOT__Basics_LF_Basics_true =>
        to_from
          (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_nandb_iso Original_LF__DOT__Basics_LF_Basics_false_iso Original_LF__DOT__Basics_LF_Basics_false_iso)
             Original_LF__DOT__Basics_LF_Basics_true_iso)
          x;
      from_to :=
        fun x : Original.LF_DOT_Basics.LF.Basics.nandb Original.LF_DOT_Basics.LF.Basics.false Original.LF_DOT_Basics.LF.Basics.false = Original.LF_DOT_Basics.LF.Basics.true =>
        seq_p_of_t
          (from_to
             (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_nandb_iso Original_LF__DOT__Basics_LF_Basics_false_iso Original_LF__DOT__Basics_LF_Basics_false_iso)
                Original_LF__DOT__Basics_LF_Basics_true_iso)
             x)
    |} Original.LF_DOT_Basics.LF.Basics.test_nandb2 imported_Original_LF__DOT__Basics_LF_Basics_test__nandb2.
Existing Instance Original_LF__DOT__Basics_LF_Basics_test__nandb2_iso.
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.test_nandb2 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_test__nandb2 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.test_nandb2 Original_LF__DOT__Basics_LF_Basics_test__nandb2_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.test_nandb2 Imported.Original_LF__DOT__Basics_LF_Basics_test__nandb2 Original_LF__DOT__Basics_LF_Basics_test__nandb2_iso := {}.