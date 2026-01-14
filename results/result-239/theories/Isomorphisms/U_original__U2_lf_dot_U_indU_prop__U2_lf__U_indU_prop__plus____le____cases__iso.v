From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

Local Open Scope nat_scope.

From IsomorphismChecker Require Export Isomorphisms.U_nat__add__iso Isomorphisms.le__iso Isomorphisms.or__iso.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_plus__le__cases : forall x x0 x1 x2 : imported_nat, imported_le (imported_Nat_add x x0) (imported_Nat_add x1 x2) -> imported_or (imported_le x x1) (imported_le x0 x2) := Imported.Original_LF__DOT__IndProp_LF_IndProp_plus__le__cases.
Instance Original_LF__DOT__IndProp_LF_IndProp_plus__le__cases_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) (x5 : nat) (x6 : imported_nat) (hx1 : rel_iso nat_iso x5 x6)
    (x7 : nat) (x8 : imported_nat) (hx2 : rel_iso nat_iso x7 x8) (x9 : (x1 + x3 <= x5 + x7)%nat) (x10 : imported_le (imported_Nat_add x2 x4) (imported_Nat_add x6 x8)),
  rel_iso (relax_Iso_Ts_Ps (le_iso (Nat_add_iso hx hx0) (Nat_add_iso hx1 hx2))) x9 x10 ->
  rel_iso (relax_Iso_Ts_Ps (or_iso (le_iso hx hx1) (le_iso hx0 hx2))) (Original.LF_DOT_IndProp.LF.IndProp.plus_le_cases x1 x3 x5 x7 x9)
    (imported_Original_LF__DOT__IndProp_LF_IndProp_plus__le__cases x2 x4 x6 x8 x10).
Admitted.
Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.plus_le_cases := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_plus__le__cases := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.plus_le_cases Original_LF__DOT__IndProp_LF_IndProp_plus__le__cases_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.plus_le_cases Imported.Original_LF__DOT__IndProp_LF_IndProp_plus__le__cases Original_LF__DOT__IndProp_LF_IndProp_plus__le__cases_iso := {}.