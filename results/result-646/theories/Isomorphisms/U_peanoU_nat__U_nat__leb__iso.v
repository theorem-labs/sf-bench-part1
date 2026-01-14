From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

From IsomorphismChecker Require Export Isomorphisms.bool__iso Isomorphisms.nat__iso.

Definition imported_PeanoNat_Nat_leb : imported_nat -> imported_nat -> imported_bool := Imported.PeanoNat_Nat_leb.

(* First prove that leb commutes with the translations *)
Definition leb_commutes : forall x1 x3 : nat,
  IsomorphismDefinitions.eq 
    (bool_to_imported (PeanoNat.Nat.leb x1 x3))
    (Imported.PeanoNat_Nat_leb (nat_to_imported x1) (nat_to_imported x3)).
Proof.
  fix IH 1.
  intros x1 x3.
  destruct x1 as [|x1']; destruct x3 as [|x3']; try apply IsomorphismDefinitions.eq_refl.
  simpl.
  apply IH.
Defined.

(* Prove that PeanoNat.Nat.leb and Imported.PeanoNat_Nat_leb are related under the isomorphisms *)
Definition PeanoNat_Nat_leb_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 -> forall (x3 : nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> rel_iso bool_iso (PeanoNat.Nat.leb x1 x3) (imported_PeanoNat_Nat_leb x2 x4).
Proof.
  intros x1 x2 H1 x3 x4 H3.
  unfold rel_iso in *.
  unfold imported_PeanoNat_Nat_leb.
  simpl in *.
  (* H1 : nat_to_imported x1 = x2, H3 : nat_to_imported x3 = x4, both in SProp *)
  (* We need to show: bool_to_imported (PeanoNat.Nat.leb x1 x3) = Imported.PeanoNat_Nat_leb x2 x4 *)
  (* Use eq_trans and f_equal2 to combine leb_commutes with H1 and H3 *)
  apply (eq_trans (leb_commutes x1 x3)).
  apply f_equal2; assumption.
Defined.

Instance PeanoNat_Nat_leb_iso_inst : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 -> forall (x3 : nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> rel_iso bool_iso (PeanoNat.Nat.leb x1 x3) (imported_PeanoNat_Nat_leb x2 x4) := PeanoNat_Nat_leb_iso.

Instance: KnownConstant PeanoNat.Nat.leb := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.PeanoNat_Nat_leb := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor PeanoNat.Nat.leb PeanoNat_Nat_leb_iso := {}.
Instance: IsoStatementProofBetween PeanoNat.Nat.leb Imported.PeanoNat_Nat_leb PeanoNat_Nat_leb_iso := {}.
