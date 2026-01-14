From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.__0__iso Isomorphisms.U_nat__add__iso Isomorphisms.U_nat__mul__iso Isomorphisms.U_s__iso Isomorphisms.le__iso.

Local Open Scope nat_scope.

Definition imported_Original_LF__DOT__AltAuto_LF_AltAuto_trans__example1 : forall x x0 x1 x2 : imported_nat,
  imported_le x (imported_Nat_add x0 (imported_Nat_mul x0 x1)) -> imported_le (imported_Nat_mul (imported_Nat_add (imported_S imported_0) x1) x0) x2 -> imported_le x x2 := Imported.Original_LF__DOT__AltAuto_LF_AltAuto_trans__example1.
Instance Original_LF__DOT__AltAuto_LF_AltAuto_trans__example1_iso : forall (x1 : Datatypes.nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : Datatypes.nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) (x5 : Datatypes.nat) (x6 : imported_nat) (hx1 : rel_iso nat_iso x5 x6)
    (x7 : Datatypes.nat) (x8 : imported_nat) (hx2 : rel_iso nat_iso x7 x8) (x9 : Peano.le x1 (Nat.add x3 (Nat.mul x3 x5))) (x10 : imported_le x2 (imported_Nat_add x4 (imported_Nat_mul x4 x6))),
  rel_iso
    {|
      to := le_iso hx (Nat_add_iso hx0 (Nat_mul_iso hx0 hx1));
      from := from (le_iso hx (Nat_add_iso hx0 (Nat_mul_iso hx0 hx1)));
      to_from := fun x : imported_le x2 (imported_Nat_add x4 (imported_Nat_mul x4 x6)) => to_from (le_iso hx (Nat_add_iso hx0 (Nat_mul_iso hx0 hx1))) x;
      from_to := fun x : Peano.le x1 (Nat.add x3 (Nat.mul x3 x5)) => seq_p_of_t (from_to (le_iso hx (Nat_add_iso hx0 (Nat_mul_iso hx0 hx1))) x)
    |} x9 x10 ->
  forall (x11 : Peano.le (Nat.mul (Nat.add 1 x5) x3) x7) (x12 : imported_le (imported_Nat_mul (imported_Nat_add (imported_S imported_0) x6) x4) x8),
  rel_iso
    {|
      to := le_iso (Nat_mul_iso (Nat_add_iso (S_iso _0_iso) hx1) hx0) hx2;
      from := from (le_iso (Nat_mul_iso (Nat_add_iso (S_iso _0_iso) hx1) hx0) hx2);
      to_from := fun x : imported_le (imported_Nat_mul (imported_Nat_add (imported_S imported_0) x6) x4) x8 => to_from (le_iso (Nat_mul_iso (Nat_add_iso (S_iso _0_iso) hx1) hx0) hx2) x;
      from_to := fun x : Peano.le (Nat.mul (Nat.add 1 x5) x3) x7 => seq_p_of_t (from_to (le_iso (Nat_mul_iso (Nat_add_iso (S_iso _0_iso) hx1) hx0) hx2) x)
    |} x11 x12 ->
  rel_iso
    {| to := le_iso hx hx2; from := from (le_iso hx hx2); to_from := fun x : imported_le x2 x8 => to_from (le_iso hx hx2) x; from_to := fun x : Peano.le x1 x7 => seq_p_of_t (from_to (le_iso hx hx2) x) |}
    (Original.LF_DOT_AltAuto.LF.AltAuto.trans_example1 x1 x3 x5 x7 x9 x11) (@imported_Original_LF__DOT__AltAuto_LF_AltAuto_trans__example1 x2 x4 x6 x8 x10 x12).
Admitted.
Instance: KnownConstant Original.LF_DOT_AltAuto.LF.AltAuto.trans_example1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__AltAuto_LF_AltAuto_trans__example1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_AltAuto.LF.AltAuto.trans_example1 Original_LF__DOT__AltAuto_LF_AltAuto_trans__example1_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_AltAuto.LF.AltAuto.trans_example1 Imported.Original_LF__DOT__AltAuto_LF_AltAuto_trans__example1 Original_LF__DOT__AltAuto_LF_AltAuto_trans__example1_iso := {}.