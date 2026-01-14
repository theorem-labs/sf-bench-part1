From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__odd__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_test__odd2 : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_odd (imported_S (imported_S (imported_S (imported_S imported_0))))) imported_Original_LF__DOT__Basics_LF_Basics_false := Imported.Original_LF__DOT__Basics_LF_Basics_test__odd2.

(* The isomorphism between two propositions in SProp (proof irrelevance) *)
Instance Original_LF__DOT__Basics_LF_Basics_test__odd2_iso : rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_odd_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))) Original_LF__DOT__Basics_LF_Basics_false_iso;
      from := from (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_odd_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))) Original_LF__DOT__Basics_LF_Basics_false_iso);
      to_from :=
        fun
          x : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_odd (imported_S (imported_S (imported_S (imported_S imported_0)))))
                imported_Original_LF__DOT__Basics_LF_Basics_false =>
        to_from (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_odd_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))) Original_LF__DOT__Basics_LF_Basics_false_iso) x;
      from_to :=
        fun x : Original.LF_DOT_Basics.LF.Basics.odd 4 = Original.LF_DOT_Basics.LF.Basics.false =>
        seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_odd_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))) Original_LF__DOT__Basics_LF_Basics_false_iso) x)
    |} Original.LF_DOT_Basics.LF.Basics.test_odd2 imported_Original_LF__DOT__Basics_LF_Basics_test__odd2.
Proof.
  unfold rel_iso. simpl.
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.test_odd2 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_test__odd2 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.test_odd2 Original_LF__DOT__Basics_LF_Basics_test__odd2_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.test_odd2 Imported.Original_LF__DOT__Basics_LF_Basics_test__odd2 Original_LF__DOT__Basics_LF_Basics_test__odd2_iso := {}.