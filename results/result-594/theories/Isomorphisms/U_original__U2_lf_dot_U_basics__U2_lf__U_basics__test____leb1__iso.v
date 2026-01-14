From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__leb__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_test__leb1 : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_leb (imported_S (imported_S imported_0)) (imported_S (imported_S imported_0)))
    imported_Original_LF__DOT__Basics_LF_Basics_true := Imported.Original_LF__DOT__Basics_LF_Basics_test__leb1.

(* The goal is to prove a rel_iso between two proofs of equivalent propositions.
   The `to` of the iso takes a Prop proof to an SProp proof.
   Since both sides are proofs of propositions, we use SProp proof irrelevance. *)
Instance Original_LF__DOT__Basics_LF_Basics_test__leb1_iso : rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_leb_iso (S_iso (S_iso _0_iso)) (S_iso (S_iso _0_iso))) Original_LF__DOT__Basics_LF_Basics_true_iso;
      from := from (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_leb_iso (S_iso (S_iso _0_iso)) (S_iso (S_iso _0_iso))) Original_LF__DOT__Basics_LF_Basics_true_iso);
      to_from :=
        fun
          x : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_leb (imported_S (imported_S imported_0)) (imported_S (imported_S imported_0)))
                imported_Original_LF__DOT__Basics_LF_Basics_true =>
        to_from (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_leb_iso (S_iso (S_iso _0_iso)) (S_iso (S_iso _0_iso))) Original_LF__DOT__Basics_LF_Basics_true_iso) x;
      from_to :=
        fun x : Original.LF_DOT_Basics.LF.Basics.leb 2 2 = Original.LF_DOT_Basics.LF.Basics.true =>
        seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_leb_iso (S_iso (S_iso _0_iso)) (S_iso (S_iso _0_iso))) Original_LF__DOT__Basics_LF_Basics_true_iso) x)
    |} Original.LF_DOT_Basics.LF.Basics.test_leb1 imported_Original_LF__DOT__Basics_LF_Basics_test__leb1.
Proof.
  unfold rel_iso. simpl.
  (* The goal is: eq (to iso Original.test_leb1) imported_test_leb1 *)
  (* Both sides are in SProp, so they are definitionally equal *)
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.test_leb1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_test__leb1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.test_leb1 Original_LF__DOT__Basics_LF_Basics_test__leb1_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.test_leb1 Imported.Original_LF__DOT__Basics_LF_Basics_test__leb1 Original_LF__DOT__Basics_LF_Basics_test__leb1_iso := {}.