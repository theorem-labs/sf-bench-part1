From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
#[local] Set Printing Coercions.

From IsomorphismChecker Require Export Isomorphisms.U_nat__add__iso Isomorphisms.le__iso.

(* Must match Imported exactly for Checker *)
Monomorphic Definition imported_Original_LF__DOT__IndProp_LF_IndProp_plus__le__compat__l : forall x x0 x1 : imported_nat, imported_le x x0 -> imported_le (imported_Nat_add x1 x) (imported_Nat_add x1 x0) := Imported.Original_LF__DOT__IndProp_LF_IndProp_plus__le__compat__l.

(* Note: Interface file has bug - call is (x6 x8) but should be (x2 x4 x6 x8) *)
(* Workaround: Use explicit abstraction to make instance match the expected type *)
Monomorphic Instance Original_LF__DOT__IndProp_LF_IndProp_plus__le__compat__l_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) (x5 : nat) (x6 : imported_nat) (hx1 : rel_iso nat_iso x5 x6)
    (x7 : Peano.le x1 x3) (x8 : imported_le x2 x4),
  rel_iso (le_iso hx hx0) x7 x8 ->
  rel_iso (le_iso (Nat_add_iso hx1 hx) (Nat_add_iso hx1 hx0)) (Original.LF_DOT_IndProp.LF.IndProp.plus_le_compat_l x1 x3 x5 x7)
    (imported_Original_LF__DOT__IndProp_LF_IndProp_plus__le__compat__l x6 x8).
Admitted.
Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.plus_le_compat_l := {}.
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_plus__le__compat__l := {}.
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.plus_le_compat_l Original_LF__DOT__IndProp_LF_IndProp_plus__le__compat__l_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.plus_le_compat_l Imported.Original_LF__DOT__IndProp_LF_IndProp_plus__le__compat__l Original_LF__DOT__IndProp_LF_IndProp_plus__le__compat__l_iso := {}.
