From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_nat__add__iso Isomorphisms.le__iso.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_plus__le__compat__l : forall x x0 x1 : imported_nat, imported_le x x0 -> imported_le (imported_Nat_add x1 x) (imported_Nat_add x1 x0) := Imported.Original_LF__DOT__IndProp_LF_IndProp_plus__le__compat__l.
Instance Original_LF__DOT__IndProp_LF_IndProp_plus__le__compat__l_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) (x5 : nat) (x6 : imported_nat) (hx1 : rel_iso nat_iso x5 x6)
    (x7 : (x1 <= x3)%nat) (x8 : imported_le x2 x4),
  rel_iso
    {| to := le_iso hx hx0; from := from (le_iso hx hx0); to_from := fun x : imported_le x2 x4 => to_from (le_iso hx hx0) x; from_to := fun x : (x1 <= x3)%nat => seq_p_of_t (from_to (le_iso hx hx0) x) |}
    x7 x8 ->
  rel_iso
    {|
      to := le_iso (Nat_add_iso hx1 hx) (Nat_add_iso hx1 hx0);
      from := from (le_iso (Nat_add_iso hx1 hx) (Nat_add_iso hx1 hx0));
      to_from := fun x : imported_le (imported_Nat_add x6 x2) (imported_Nat_add x6 x4) => to_from (le_iso (Nat_add_iso hx1 hx) (Nat_add_iso hx1 hx0)) x;
      from_to := fun x : (x5 + x1 <= x5 + x3)%nat => seq_p_of_t (from_to (le_iso (Nat_add_iso hx1 hx) (Nat_add_iso hx1 hx0)) x)
    |} (Original.LF_DOT_IndProp.LF.IndProp.plus_le_compat_l x1 x3 x5 x7) (imported_Original_LF__DOT__IndProp_LF_IndProp_plus__le__compat__l x6 x8).
Proof.
  intros. unfold rel_iso. simpl. apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.plus_le_compat_l := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_plus__le__compat__l := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.plus_le_compat_l Original_LF__DOT__IndProp_LF_IndProp_plus__le__compat__l_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.plus_le_compat_l Imported.Original_LF__DOT__IndProp_LF_IndProp_plus__le__compat__l Original_LF__DOT__IndProp_LF_IndProp_plus__le__compat__l_iso := {}.