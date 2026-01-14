From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__nostutter__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Isomorphisms.__0__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_test__nostutter__3 : imported_Original_LF__DOT__IndProp_LF_IndProp_nostutter
    (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (imported_S (imported_S imported_0))))) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat)) := Imported.Original_LF__DOT__IndProp_LF_IndProp_test__nostutter__3.

(* Both nostutter types are empty inductives in SProp. The isomorphism between them
   maps elements to elements, but since the type is empty, any two elements are equal
   in SProp by proof irrelevance (SProp collapses all proofs). *)
Instance Original_LF__DOT__IndProp_LF_IndProp_test__nostutter__3_iso : rel_iso
    (Original_LF__DOT__IndProp_LF_IndProp_nostutter_iso (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso)))
    Original.LF_DOT_IndProp.LF.IndProp.test_nostutter_3 imported_Original_LF__DOT__IndProp_LF_IndProp_test__nostutter__3.
Proof.
  unfold rel_iso.
  (* Both Original.nostutter and Imported.nostutter are empty inductives. 
     The iso's `to` function uses destruct, which eliminates Original.test_nostutter_3.
     But we can't destruct an axiom for an empty type directly.
     Instead, we use the fact that the target type is SProp and all SProp proofs are equal. *)
  (* The to function of the nostutter_iso destructs the argument (which is in an empty type),
     so applying it to test_nostutter_3 gives us something that lives in SProp.
     In SProp, all proofs of the same type are definitionally equal. *)
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.test_nostutter_3 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_test__nostutter__3 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.test_nostutter_3 Original_LF__DOT__IndProp_LF_IndProp_test__nostutter__3_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.test_nostutter_3 Imported.Original_LF__DOT__IndProp_LF_IndProp_test__nostutter__3 Original_LF__DOT__IndProp_LF_IndProp_test__nostutter__3_iso := {}.