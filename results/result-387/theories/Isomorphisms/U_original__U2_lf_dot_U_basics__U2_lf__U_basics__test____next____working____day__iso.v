From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__next____working____day__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__saturday__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__tuesday__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_test__next__working__day : imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__Basics_LF_Basics_next__working__day (imported_Original_LF__DOT__Basics_LF_Basics_next__working__day imported_Original_LF__DOT__Basics_LF_Basics_saturday))
    imported_Original_LF__DOT__Basics_LF_Basics_tuesday := Imported.Original_LF__DOT__Basics_LF_Basics_test__next__working__day.

(* Since both Original.LF_DOT_Basics.LF.Basics.test_next_working_day and Imported are axioms/admitted,
   the isomorphism is between two propositions that should be true. 
   The imported version is an axiom in SProp, the original is Admitted (so also an axiom).
   We use the fact that both equalities hold definitionally after unfolding. *)

Instance Original_LF__DOT__Basics_LF_Basics_test__next__working__day_iso : rel_iso
    {|
      to :=
        Corelib_Init_Logic_eq_iso
          (Original_LF__DOT__Basics_LF_Basics_next__working__day_iso (Original_LF__DOT__Basics_LF_Basics_next__working__day_iso Original_LF__DOT__Basics_LF_Basics_saturday_iso))
          Original_LF__DOT__Basics_LF_Basics_tuesday_iso;
      from :=
        from
          (Corelib_Init_Logic_eq_iso
             (Original_LF__DOT__Basics_LF_Basics_next__working__day_iso (Original_LF__DOT__Basics_LF_Basics_next__working__day_iso Original_LF__DOT__Basics_LF_Basics_saturday_iso))
             Original_LF__DOT__Basics_LF_Basics_tuesday_iso);
      to_from :=
        fun
          x : imported_Corelib_Init_Logic_eq
                (imported_Original_LF__DOT__Basics_LF_Basics_next__working__day (imported_Original_LF__DOT__Basics_LF_Basics_next__working__day imported_Original_LF__DOT__Basics_LF_Basics_saturday))
                imported_Original_LF__DOT__Basics_LF_Basics_tuesday =>
        to_from
          (Corelib_Init_Logic_eq_iso
             (Original_LF__DOT__Basics_LF_Basics_next__working__day_iso (Original_LF__DOT__Basics_LF_Basics_next__working__day_iso Original_LF__DOT__Basics_LF_Basics_saturday_iso))
             Original_LF__DOT__Basics_LF_Basics_tuesday_iso)
          x;
      from_to :=
        fun
          x : Original.LF_DOT_Basics.LF.Basics.next_working_day (Original.LF_DOT_Basics.LF.Basics.next_working_day Original.LF_DOT_Basics.LF.Basics.saturday) =
              Original.LF_DOT_Basics.LF.Basics.tuesday =>
        seq_p_of_t
          (from_to
             (Corelib_Init_Logic_eq_iso
                (Original_LF__DOT__Basics_LF_Basics_next__working__day_iso (Original_LF__DOT__Basics_LF_Basics_next__working__day_iso Original_LF__DOT__Basics_LF_Basics_saturday_iso))
                Original_LF__DOT__Basics_LF_Basics_tuesday_iso)
             x)
    |} Original.LF_DOT_Basics.LF.Basics.test_next_working_day imported_Original_LF__DOT__Basics_LF_Basics_test__next__working__day.
Proof.
  unfold rel_iso. simpl.
  unfold imported_Original_LF__DOT__Basics_LF_Basics_test__next__working__day.
  unfold imported_Corelib_Init_Logic_eq.
  (* Both are proofs of an equality that holds definitionally, so we can prove it directly *)
  apply IsomorphismDefinitions.eq_refl.
Qed.

Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.test_next_working_day := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_test__next__working__day := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.test_next_working_day Original_LF__DOT__Basics_LF_Basics_test__next__working__day_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.test_next_working_day Imported.Original_LF__DOT__Basics_LF_Basics_test__next__working__day Original_LF__DOT__Basics_LF_Basics_test__next__working__day_iso := {}.