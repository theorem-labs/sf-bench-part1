From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_nat : Type := Imported.nat.

(* Isomorphism between Coq nat and Lean nat *)
Fixpoint nat_to_imported (n : nat) : imported_nat :=
  match n with
  | O => Imported.nat_O
  | Datatypes.S m => Imported.nat_S (nat_to_imported m)
  end.

Fixpoint nat_from_imported (n : imported_nat) : nat :=
  match n with
  | Imported.nat_O => O
  | Imported.nat_S m => Datatypes.S (nat_from_imported m)
  end.

Lemma nat_to_from : forall n, nat_to_imported (nat_from_imported n) = n.
Proof.
  fix IH 1.
  intro n; destruct n as [|m].
  - reflexivity.
  - simpl. f_equal. apply IH.
Qed.

Lemma nat_from_to : forall n, nat_from_imported (nat_to_imported n) = n.
Proof.
  fix IH 1.
  intro n; destruct n as [|m].
  - reflexivity.
  - simpl. f_equal. apply IH.
Qed.

Instance nat_iso : Iso nat imported_nat.
Proof.
  unshelve eapply Build_Iso.
  - exact nat_to_imported.
  - exact nat_from_imported.
  - intro n. rewrite nat_to_from. apply IsomorphismDefinitions.eq_refl.
  - intro n. rewrite nat_from_to. apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor nat nat_iso := {}.
Instance: IsoStatementProofBetween nat Imported.nat nat_iso := {}.