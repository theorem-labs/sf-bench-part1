From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Definition imported_S : imported_nat -> imported_nat := Imported.S.

Lemma nat_to_imported_S : forall n, nat_to_imported (S n) = Imported.nat_S (nat_to_imported n).
Proof. reflexivity. Qed.

Instance S_iso : forall (x1 : nat) (x2 : imported_nat), rel_iso nat_iso x1 x2 -> rel_iso nat_iso (S x1) (imported_S x2).
Proof.
  intros x1 x2 H.
  unfold rel_iso in *. simpl in *.
  unfold imported_S. unfold Imported.S.
  (* H : eq (nat_to_imported x1) x2 *)
  (* Goal: eq (nat_to_imported (S x1)) (Imported.nat_S x2) *)
  destruct H.
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant S := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.S := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor S S_iso := {}.
Instance: IsoStatementProofBetween S Imported.S S_iso := {}.