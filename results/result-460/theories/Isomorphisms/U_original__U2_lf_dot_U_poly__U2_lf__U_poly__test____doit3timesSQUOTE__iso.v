From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso. (* for speed *)

From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__doit3times__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__negb__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.

Definition imported_Original_LF__DOT__Poly_LF_Poly_test__doit3times' : imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__Poly_LF_Poly_doit3times (fun x : imported_Original_LF__DOT__Basics_LF_Basics_bool => imported_Original_LF__DOT__Basics_LF_Basics_negb x)
       imported_Original_LF__DOT__Basics_LF_Basics_true)
    imported_Original_LF__DOT__Basics_LF_Basics_false := Imported.Original_LF__DOT__Poly_LF_Poly_test__doit3times'.

(* The original is Admitted, the isomorphism is an allowed axiom *)
(* Use a simple Iso between the two propositions *)

Definition lhs_type : Prop := Original.LF_DOT_Poly.LF.Poly.doit3times Original.LF_DOT_Basics.LF.Basics.negb Original.LF_DOT_Basics.LF.Basics.true = Original.LF_DOT_Basics.LF.Basics.false.
Definition rhs_type : SProp := imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__Poly_LF_Poly_doit3times (fun x : imported_Original_LF__DOT__Basics_LF_Basics_bool => imported_Original_LF__DOT__Basics_LF_Basics_negb x)
       imported_Original_LF__DOT__Basics_LF_Basics_true)
    imported_Original_LF__DOT__Basics_LF_Basics_false.

Definition simple_iso : Iso lhs_type rhs_type.
Proof.
  unshelve eapply Build_Iso.
  - intro H. exact imported_Original_LF__DOT__Poly_LF_Poly_test__doit3times'.
  - intro H. exact Original.LF_DOT_Poly.LF.Poly.test_doit3times'.
  - intro x. apply IsomorphismDefinitions.eq_refl.
  - intro x. apply sUIPt.
Defined.

Instance Original_LF__DOT__Poly_LF_Poly_test__doit3times'_iso : rel_iso simple_iso
    Original.LF_DOT_Poly.LF.Poly.test_doit3times' imported_Original_LF__DOT__Poly_LF_Poly_test__doit3times'.
Proof.
  unfold rel_iso. simpl.
  (* The goal should be showing that to simple_iso test_doit3times' = imported_test_doit3times' *)
  apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_Poly.LF.Poly.test_doit3times' := {}.
Instance: KnownConstant Imported.Original_LF__DOT__Poly_LF_Poly_test__doit3times' := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.test_doit3times' Original_LF__DOT__Poly_LF_Poly_test__doit3times'_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.test_doit3times' Imported.Original_LF__DOT__Poly_LF_Poly_test__doit3times' Original_LF__DOT__Poly_LF_Poly_test__doit3times'_iso := {}.
