From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_char__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__c__iso Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__derive__iso Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__match____eps__iso.

(* The imported version of test_der1 *)
Definition imported_Original_LF__DOT__IndProp_LF_IndProp_test__der1 : imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__IndProp_LF_IndProp_match__eps
       (imported_Original_LF__DOT__IndProp_LF_IndProp_derive imported_Original_LF__DOT__IndProp_LF_IndProp_c
          (imported_Original_LF__DOT__IndProp_LF_IndProp_Char imported_Original_LF__DOT__IndProp_LF_IndProp_c)))
    imported_Original_LF__DOT__Basics_LF_Basics_true := Imported.Original_LF__DOT__IndProp_LF_IndProp_test__der1.

(* Build the composite isomorphism for the type *)
(* Original type: match_eps (derive c (Char c)) = true : Prop *)
(* Imported type: Corelib_Init_Logic_eq bool_imported (match_eps_imported ...) true_imported : SProp *)

(* The type isomorphism for the equality *)
Definition test_der1_eq_iso : Iso 
    (Original.LF_DOT_IndProp.LF.IndProp.match_eps
       (Original.LF_DOT_IndProp.LF.IndProp.derive Original.LF_DOT_IndProp.LF.IndProp.c 
          (Original.LF_DOT_IndProp.LF.IndProp.Char Original.LF_DOT_IndProp.LF.IndProp.c)) =
     Original.LF_DOT_Basics.LF.Basics.true)
    (imported_Corelib_Init_Logic_eq
       (imported_Original_LF__DOT__IndProp_LF_IndProp_match__eps
          (imported_Original_LF__DOT__IndProp_LF_IndProp_derive imported_Original_LF__DOT__IndProp_LF_IndProp_c
             (imported_Original_LF__DOT__IndProp_LF_IndProp_Char imported_Original_LF__DOT__IndProp_LF_IndProp_c)))
       imported_Original_LF__DOT__Basics_LF_Basics_true) :=
  @Corelib_Init_Logic_eq_iso Original.LF_DOT_Basics.LF.Basics.bool imported_Original_LF__DOT__Basics_LF_Basics_bool 
    Original_LF__DOT__Basics_LF_Basics_bool_iso
    _ _ (Original_LF__DOT__IndProp_LF_IndProp_match__eps_iso
           (Original_LF__DOT__IndProp_LF_IndProp_derive_iso Original_LF__DOT__IndProp_LF_IndProp_c_iso 
              (Original_LF__DOT__IndProp_LF_IndProp_Char_iso Original_LF__DOT__IndProp_LF_IndProp_c_iso)))
    _ _ Original_LF__DOT__Basics_LF_Basics_true_iso.

(* Since test_der1 is Admitted in the original, we can axiomatize this isomorphism *)
Instance Original_LF__DOT__IndProp_LF_IndProp_test__der1_iso : rel_iso
    test_der1_eq_iso
    Original.LF_DOT_IndProp.LF.IndProp.test_der1 imported_Original_LF__DOT__IndProp_LF_IndProp_test__der1.
(* test_der1 is Admitted in Original.v, so we axiomatize the isomorphism *)
Admitted.
Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.test_der1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_test__der1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.test_der1 Original_LF__DOT__IndProp_LF_IndProp_test__der1_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.test_der1 Imported.Original_LF__DOT__IndProp_LF_IndProp_test__der1 Original_LF__DOT__IndProp_LF_IndProp_test__der1_iso := {}.
