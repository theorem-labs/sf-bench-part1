From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.__0__iso Isomorphisms.U_nat__add__iso Isomorphisms.U_nat__mul__iso Isomorphisms.U_s__iso Isomorphisms.le__iso.

Monomorphic Definition imported_Original_LF__DOT__AltAuto_LF_AltAuto_trans__example1' : forall x x0 x1 x2 : imported_nat,
  imported_le x (imported_Nat_add x0 (imported_Nat_mul x0 x1)) -> imported_le (imported_Nat_mul (imported_Nat_add (imported_S imported_0) x1) x0) x2 -> imported_le x x2 := Imported.Original_LF__DOT__AltAuto_LF_AltAuto_trans__example1'.

Monomorphic Instance Original_LF__DOT__AltAuto_LF_AltAuto_trans__example1'_iso : forall (a1 : nat) (a2 : imported_nat) (ha : rel_iso nat_iso a1 a2) (b1 : nat) (b2 : imported_nat) (hb : rel_iso nat_iso b1 b2) (c1 : nat) (c2 : imported_nat) (hc : rel_iso nat_iso c1 c2)
    (d1 : nat) (d2 : imported_nat) (hd : rel_iso nat_iso d1 d2) (pf1 : le a1 (b1 + b1 * c1)) (pf2 : imported_le a2 (imported_Nat_add b2 (imported_Nat_mul b2 c2))),
  rel_iso (le_iso ha (Nat_add_iso hb (Nat_mul_iso hb hc))) pf1 pf2 ->
  forall (pf3 : le ((1 + c1) * b1) d1) (pf4 : imported_le (imported_Nat_mul (imported_Nat_add (imported_S imported_0) c2) b2) d2),
  rel_iso (le_iso (Nat_mul_iso (Nat_add_iso (S_iso _0_iso) hc) hb) hd) pf3 pf4 ->
  rel_iso (le_iso ha hd) (Original.LF_DOT_AltAuto.LF.AltAuto.trans_example1' a1 b1 c1 d1 pf1 pf3) (@imported_Original_LF__DOT__AltAuto_LF_AltAuto_trans__example1' a2 b2 c2 d2 pf2 pf4).
Admitted.
Instance: KnownConstant Original.LF_DOT_AltAuto.LF.AltAuto.trans_example1' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__AltAuto_LF_AltAuto_trans__example1' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_AltAuto.LF.AltAuto.trans_example1' Original_LF__DOT__AltAuto_LF_AltAuto_trans__example1'_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_AltAuto.LF.AltAuto.trans_example1' Imported.Original_LF__DOT__AltAuto_LF_AltAuto_trans__example1' Original_LF__DOT__AltAuto_LF_AltAuto_trans__example1'_iso := {}.
