From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__odd__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_test__odd1 : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_odd (imported_S imported_0)) imported_Original_LF__DOT__Basics_LF_Basics_true := Imported.Original_LF__DOT__Basics_LF_Basics_test__odd1.

(* The isomorphism is between proofs of equality - both sides are in SProp-like types *)
(* We need to show that to(test_odd1) = imported_test_odd1 in SProp *)
Instance Original_LF__DOT__Basics_LF_Basics_test__odd1_iso : rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_odd_iso (S_iso _0_iso)) Original_LF__DOT__Basics_LF_Basics_true_iso;
      from := from (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_odd_iso (S_iso _0_iso)) Original_LF__DOT__Basics_LF_Basics_true_iso);
      to_from :=
        fun x : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_odd (imported_S imported_0)) imported_Original_LF__DOT__Basics_LF_Basics_true =>
        to_from (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_odd_iso (S_iso _0_iso)) Original_LF__DOT__Basics_LF_Basics_true_iso) x;
      from_to :=
        fun x : Original.LF_DOT_Basics.LF.Basics.odd 1 = Original.LF_DOT_Basics.LF.Basics.true =>
        seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_odd_iso (S_iso _0_iso)) Original_LF__DOT__Basics_LF_Basics_true_iso) x)
    |} Original.LF_DOT_Basics.LF.Basics.test_odd1 imported_Original_LF__DOT__Basics_LF_Basics_test__odd1.
Proof.
  (* Both are proofs of equality types - the original in Prop, the imported in SProp *)
  (* rel_iso here means: to test_odd1 = imported_test_odd1 in SProp *)
  (* Since the target is SProp (imported_Corelib_Init_Logic_eq), any two proofs are equal *)
  unfold rel_iso.
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.test_odd1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_test__odd1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.test_odd1 Original_LF__DOT__Basics_LF_Basics_test__odd1_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.test_odd1 Imported.Original_LF__DOT__Basics_LF_Basics_test__odd1 Original_LF__DOT__Basics_LF_Basics_test__odd1_iso := {}.