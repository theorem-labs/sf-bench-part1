From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_nat__add__iso Isomorphisms.le__iso.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_plus__le__compat__r : forall x x0 x1 : imported_nat, imported_le x x0 -> imported_le (imported_Nat_add x x1) (imported_Nat_add x0 x1) := Imported.Original_LF__DOT__IndProp_LF_IndProp_plus__le__compat__r.

(* The isomorphism proof for plus_le_compat_r *)
(* This theorem is Admitted in Original.v, so we use the axiom from Imported *)
(* The rel_iso is an SProp, so we just need to show the types match *)
Instance Original_LF__DOT__IndProp_LF_IndProp_plus__le__compat__r_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) (x5 : nat) (x6 : imported_nat) (hx1 : rel_iso nat_iso x5 x6)
    (x7 : Peano.le x1 x3) (x8 : imported_le x2 x4),
  rel_iso
    {| to := le_iso hx hx0; from := from (le_iso hx hx0); to_from := fun x : imported_le x2 x4 => to_from (le_iso hx hx0) x; from_to := fun x : Peano.le x1 x3 => seq_p_of_t (from_to (le_iso hx hx0) x) |}
    x7 x8 ->
  rel_iso
    {|
      to := le_iso (Nat_add_iso hx hx1) (Nat_add_iso hx0 hx1);
      from := from (le_iso (Nat_add_iso hx hx1) (Nat_add_iso hx0 hx1));
      to_from := fun x : imported_le (imported_Nat_add x2 x6) (imported_Nat_add x4 x6) => to_from (le_iso (Nat_add_iso hx hx1) (Nat_add_iso hx0 hx1)) x;
      from_to := fun x : Peano.le (Nat.add x1 x5) (Nat.add x3 x5) => seq_p_of_t (from_to (le_iso (Nat_add_iso hx hx1) (Nat_add_iso hx0 hx1)) x)
    |} (Original.LF_DOT_IndProp.LF.IndProp.plus_le_compat_r x1 x3 x5 x7) (imported_Original_LF__DOT__IndProp_LF_IndProp_plus__le__compat__r x6 x8).
Proof.
  intros x1 x2 hx x3 x4 hx0 x5 x6 hx1 x7 x8 Hrel.
  (* rel_iso for SProp is trivial since imported_le lives in SProp *)
  unfold rel_iso. simpl.
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.plus_le_compat_r := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_plus__le__compat__r := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.plus_le_compat_r Original_LF__DOT__IndProp_LF_IndProp_plus__le__compat__r_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.plus_le_compat_r Imported.Original_LF__DOT__IndProp_LF_IndProp_plus__le__compat__r Original_LF__DOT__IndProp_LF_IndProp_plus__le__compat__r_iso := {}.