From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_nat__add__iso Isomorphisms.le__iso.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_le__plus__l : forall x x0 : imported_nat, imported_le x (imported_Nat_add x x0) := Imported.Original_LF__DOT__IndProp_LF_IndProp_le__plus__l.
Instance Original_LF__DOT__IndProp_LF_IndProp_le__plus__l_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4),
  rel_iso
    {|
      to := le_iso hx (Nat_add_iso hx hx0);
      from := from (le_iso hx (Nat_add_iso hx hx0));
      to_from := fun x : imported_le x2 (imported_Nat_add x2 x4) => to_from (le_iso hx (Nat_add_iso hx hx0)) x;
      from_to := fun x : (x1 <= x1 + x3)%nat => seq_p_of_t (from_to (le_iso hx (Nat_add_iso hx hx0)) x)
    |} (Original.LF_DOT_IndProp.LF.IndProp.le_plus_l x1 x3) (imported_Original_LF__DOT__IndProp_LF_IndProp_le__plus__l x2 x4).
Proof.
  intros.
  unfold rel_iso. simpl.
  (* Both sides are in SProp which is proof irrelevant *)
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.le_plus_l := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_le__plus__l := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.le_plus_l Original_LF__DOT__IndProp_LF_IndProp_le__plus__l_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.le_plus_l Imported.Original_LF__DOT__IndProp_LF_IndProp_le__plus__l Original_LF__DOT__IndProp_LF_IndProp_le__plus__l_iso := {}.