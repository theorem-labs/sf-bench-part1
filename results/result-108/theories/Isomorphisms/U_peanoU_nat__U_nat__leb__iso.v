From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.bool__iso Isomorphisms.nat__iso.

Definition imported_PeanoNat_Nat_leb : imported_nat -> imported_nat -> imported_bool := Imported.nat_leb.

(* Helper functions for conversion *)
Definition bool_to_mybool (b : bool) : imported_bool :=
  match b with true => Imported.mybool_mytrue | false => Imported.mybool_myfalse end.

(* Helper lemma: leb is preserved under the isomorphism *)
Lemma leb_iso_helper : forall n m,
  IsomorphismDefinitions.eq 
    (bool_to_mybool (PeanoNat.Nat.leb n m))
    (Imported.nat_leb (nat_to_imported n) (nat_to_imported m)).
Proof.
  fix IH 1.
  intros n m.
  destruct n as [|n']; destruct m as [|m']; simpl.
  - apply IsomorphismDefinitions.eq_refl.
  - apply IsomorphismDefinitions.eq_refl.
  - apply IsomorphismDefinitions.eq_refl.
  - apply IH.
Defined.

Instance PeanoNat_Nat_leb_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 -> forall (x3 : nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> rel_iso bool_iso (PeanoNat.Nat.leb x1 x3) (imported_PeanoNat_Nat_leb x2 x4).
Proof.
  intros x1 x2 H12 x3 x4 H34.
  set (H12' := proj_rel_iso H12).
  set (H34' := proj_rel_iso H34).
  constructor.
  simpl in *.
  unfold imported_PeanoNat_Nat_leb.
  destruct H12'. destruct H34'.
  apply leb_iso_helper.
Defined.
Instance: KnownConstant PeanoNat.Nat.leb := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.nat_leb := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor PeanoNat.Nat.leb PeanoNat_Nat_leb_iso := {}.
Instance: IsoStatementProofBetween PeanoNat.Nat.leb Imported.nat_leb PeanoNat_Nat_leb_iso := {}.