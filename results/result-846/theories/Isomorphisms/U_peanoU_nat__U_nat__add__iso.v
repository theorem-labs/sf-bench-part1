From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Definition imported_PeanoNat_Nat_add : imported_nat -> imported_nat -> imported_nat := Imported.PeanoNat_Nat_add.

(* Helper lemma: addition commutes with the isomorphism *)
Lemma nat_add_compat : forall x1 x3, 
  IsomorphismDefinitions.eq (to nat_iso (x1 + x3)) (Imported.PeanoNat_Nat_add (to nat_iso x1) (to nat_iso x3)).
Proof.
  intros x1 x3. induction x1.
  - simpl. apply IsomorphismDefinitions.eq_refl.
  - simpl. apply (IsoEq.f_equal Imported.nat_S). exact IHx1.
Defined.

Instance PeanoNat_Nat_add_iso : forall (x1 : nat) (x2 : imported_nat), rel_iso nat_iso x1 x2 -> forall (x3 : nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> rel_iso nat_iso (x1 + x3) (imported_PeanoNat_Nat_add x2 x4).
Proof.
  intros x1 x2 H12 x3 x4 H34.
  unfold rel_iso in *.
  simpl in *.
  unfold imported_PeanoNat_Nat_add.
  (* Transport along H12 and H34 *)
  apply (IsoEq.eq_trans (nat_add_compat x1 x3)).
  apply (IsoEq.f_equal2 Imported.PeanoNat_Nat_add H12 H34).
Defined.
Instance: KnownConstant PeanoNat.Nat.add := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.PeanoNat_Nat_add := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor PeanoNat.Nat.add PeanoNat_Nat_add_iso := {}.
Instance: IsoStatementProofBetween PeanoNat.Nat.add Imported.PeanoNat_Nat_add PeanoNat_Nat_add_iso := {}.