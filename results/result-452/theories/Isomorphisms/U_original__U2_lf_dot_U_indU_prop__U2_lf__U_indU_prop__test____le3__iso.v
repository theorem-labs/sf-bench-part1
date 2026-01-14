From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

Local Open Scope nat_scope.

From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_nat__add__iso Isomorphisms.U_s__iso Isomorphisms.le__iso.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_test__le3 : imported_le (imported_S (imported_S imported_0)) (imported_S imported_0) ->
  imported_Corelib_Init_Logic_eq (imported_Nat_add (imported_S (imported_S imported_0)) (imported_S (imported_S imported_0)))
    (imported_S (imported_S (imported_S (imported_S (imported_S imported_0))))) := Imported.Original_LF__DOT__IndProp_LF_IndProp_test__le3.
Instance Original_LF__DOT__IndProp_LF_IndProp_test__le3_iso : forall (x1 : (2 <= 1)%nat) (x2 : imported_le (imported_S (imported_S imported_0)) (imported_S imported_0)),
  rel_iso
    {|
      to := le_iso (S_iso (S_iso _0_iso)) (S_iso _0_iso);
      from := from (le_iso (S_iso (S_iso _0_iso)) (S_iso _0_iso));
      to_from := fun x : imported_le (imported_S (imported_S imported_0)) (imported_S imported_0) => to_from (le_iso (S_iso (S_iso _0_iso)) (S_iso _0_iso)) x;
      from_to := fun x : (2 <= 1)%nat => seq_p_of_t (from_to (le_iso (S_iso (S_iso _0_iso)) (S_iso _0_iso)) x)
    |} x1 x2 ->
  rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso (Nat_add_iso (S_iso (S_iso _0_iso)) (S_iso (S_iso _0_iso))) (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))));
      from := from (Corelib_Init_Logic_eq_iso (Nat_add_iso (S_iso (S_iso _0_iso)) (S_iso (S_iso _0_iso))) (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))));
      to_from :=
        fun
          x : imported_Corelib_Init_Logic_eq (imported_Nat_add (imported_S (imported_S imported_0)) (imported_S (imported_S imported_0)))
                (imported_S (imported_S (imported_S (imported_S (imported_S imported_0))))) =>
        to_from (Corelib_Init_Logic_eq_iso (Nat_add_iso (S_iso (S_iso _0_iso)) (S_iso (S_iso _0_iso))) (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))) x;
      from_to := fun x : 2 + 2 = 5 => seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso (Nat_add_iso (S_iso (S_iso _0_iso)) (S_iso (S_iso _0_iso))) (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))) x)
    |} (Original.LF_DOT_IndProp.LF.IndProp.test_le3 x1) (imported_Original_LF__DOT__IndProp_LF_IndProp_test__le3 x2).
Proof.
  (* x1 : (2 <= 1)%nat which is impossible *)
  (* The goal is about rel_iso on the results of applying test_le3 to impossible inputs *)
  (* Since the result is in SProp (imported_Corelib_Init_Logic_eq), proof irrelevance applies *)
  intros x1 x2 Hrel.
  (* Unfold rel_iso - it's just eq in SProp *)
  unfold rel_iso. simpl.
  (* The output is in SProp, so everything is definitionally equal *)
  exact IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.test_le3 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_test__le3 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.test_le3 Original_LF__DOT__IndProp_LF_IndProp_test__le3_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.test_le3 Imported.Original_LF__DOT__IndProp_LF_IndProp_test__le3 Original_LF__DOT__IndProp_LF_IndProp_test__le3_iso := {}.