From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_char__iso Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_star__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__c__iso Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__derive__iso Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__match____eps__iso.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_test__der5 : imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__IndProp_LF_IndProp_match__eps
       (imported_Original_LF__DOT__IndProp_LF_IndProp_derive imported_Original_LF__DOT__IndProp_LF_IndProp_c
          (imported_Original_LF__DOT__IndProp_LF_IndProp_Star (imported_Original_LF__DOT__IndProp_LF_IndProp_Char imported_Original_LF__DOT__IndProp_LF_IndProp_c))))
    imported_Original_LF__DOT__Basics_LF_Basics_true := Imported.Original_LF__DOT__IndProp_LF_IndProp_test__der5.

(* Build the full iso for the eq types *)
Definition test_der5_type_iso : Iso 
  (Original.LF_DOT_IndProp.LF.IndProp.match_eps
     (Original.LF_DOT_IndProp.LF.IndProp.derive Original.LF_DOT_IndProp.LF.IndProp.c
        (Original.LF_DOT_IndProp.LF.IndProp.Star (Original.LF_DOT_IndProp.LF.IndProp.Char Original.LF_DOT_IndProp.LF.IndProp.c))) =
   Original.LF_DOT_Basics.LF.Basics.true)
  (imported_Corelib_Init_Logic_eq
     (imported_Original_LF__DOT__IndProp_LF_IndProp_match__eps
        (imported_Original_LF__DOT__IndProp_LF_IndProp_derive imported_Original_LF__DOT__IndProp_LF_IndProp_c
           (imported_Original_LF__DOT__IndProp_LF_IndProp_Star (imported_Original_LF__DOT__IndProp_LF_IndProp_Char imported_Original_LF__DOT__IndProp_LF_IndProp_c))))
     imported_Original_LF__DOT__Basics_LF_Basics_true) :=
  @Corelib_Init_Logic_eq_iso 
    Original.LF_DOT_Basics.LF.Basics.bool
    imported_Original_LF__DOT__Basics_LF_Basics_bool
    Original_LF__DOT__Basics_LF_Basics_bool_iso
    _ _
    (Original_LF__DOT__IndProp_LF_IndProp_match__eps_iso
       (Original_LF__DOT__IndProp_LF_IndProp_derive_iso Original_LF__DOT__IndProp_LF_IndProp_c_iso
          (Original_LF__DOT__IndProp_LF_IndProp_Star_iso (Original_LF__DOT__IndProp_LF_IndProp_Char_iso Original_LF__DOT__IndProp_LF_IndProp_c_iso))))
    _ _
    Original_LF__DOT__Basics_LF_Basics_true_iso.

Instance Original_LF__DOT__IndProp_LF_IndProp_test__der5_iso : rel_iso
    test_der5_type_iso
    Original.LF_DOT_IndProp.LF.IndProp.test_der5 imported_Original_LF__DOT__IndProp_LF_IndProp_test__der5.
Proof.
  (* rel_iso i x y := eq (to i x) y *)
  unfold rel_iso.
  (* Goal: eq (to test_der5_type_iso Original.LF_DOT_IndProp.LF.IndProp.test_der5) 
              imported_Original_LF__DOT__IndProp_LF_IndProp_test__der5 *)
  (* Both sides are in SProp, so this is trivial *)
  exact (IsomorphismDefinitions.eq_refl _).
Defined.
Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.test_der5 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_test__der5 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.test_der5 Original_LF__DOT__IndProp_LF_IndProp_test__der5_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.test_der5 Imported.Original_LF__DOT__IndProp_LF_IndProp_test__der5 Original_LF__DOT__IndProp_LF_IndProp_test__der5_iso := {}.