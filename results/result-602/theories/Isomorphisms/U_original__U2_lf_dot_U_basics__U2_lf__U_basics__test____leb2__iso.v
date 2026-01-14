From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__leb__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_test__leb2 : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_leb (imported_S (imported_S imported_0)) (imported_S (imported_S (imported_S (imported_S imported_0)))))
    imported_Original_LF__DOT__Basics_LF_Basics_true := Imported.Original_LF__DOT__Basics_LF_Basics_test__leb2.

(* The isomorphism for test_leb2 relates the original Admitted axiom to our imported axiom.
   Since test_leb2 is an axiom in the original that is allowed (per the problem statement),
   we use the isomorphism infrastructure. Both sides represent the same proposition. *)
Instance Original_LF__DOT__Basics_LF_Basics_test__leb2_iso : rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_leb_iso (S_iso (S_iso _0_iso)) (S_iso (S_iso (S_iso (S_iso _0_iso))))) Original_LF__DOT__Basics_LF_Basics_true_iso;
      from := from (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_leb_iso (S_iso (S_iso _0_iso)) (S_iso (S_iso (S_iso (S_iso _0_iso))))) Original_LF__DOT__Basics_LF_Basics_true_iso);
      to_from :=
        fun
          x : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_leb (imported_S (imported_S imported_0)) (imported_S (imported_S (imported_S (imported_S imported_0)))))
                imported_Original_LF__DOT__Basics_LF_Basics_true =>
        to_from (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_leb_iso (S_iso (S_iso _0_iso)) (S_iso (S_iso (S_iso (S_iso _0_iso))))) Original_LF__DOT__Basics_LF_Basics_true_iso) x;
      from_to :=
        fun x : Original.LF_DOT_Basics.LF.Basics.leb 2 4 = Original.LF_DOT_Basics.LF.Basics.true =>
        seq_p_of_t
          (from_to (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_leb_iso (S_iso (S_iso _0_iso)) (S_iso (S_iso (S_iso (S_iso _0_iso))))) Original_LF__DOT__Basics_LF_Basics_true_iso) x)
    |} Original.LF_DOT_Basics.LF.Basics.test_leb2 imported_Original_LF__DOT__Basics_LF_Basics_test__leb2.
Proof.
  unfold rel_iso. simpl.
  (* The goal should be showing that the original test_leb2 maps to the imported one *)
  (* Since both are axioms about the same proposition, we need to show they are related *)
  (* The to function applied to the original gives us an element of the imported SProp type *)
  (* We need IsomorphismDefinitions.eq between to(original) and imported *)
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.test_leb2 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_test__leb2 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.test_leb2 Original_LF__DOT__Basics_LF_Basics_test__leb2_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.test_leb2 Imported.Original_LF__DOT__Basics_LF_Basics_test__leb2 Original_LF__DOT__Basics_LF_Basics_test__leb2_iso := {}.