From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

(* The exported type is Imported.nat *)
Definition imported_nat : Type := Imported.nat.

(* Define the isomorphism between nat and Imported.nat *)
Fixpoint nat_to_imported (n : nat) : Imported.nat :=
  match n with
  | O => Imported.nat_O
  | S n' => Imported.nat_S (nat_to_imported n')
  end.

Fixpoint imported_to_nat (n : Imported.nat) : nat :=
  match n with
  | Imported.nat_O => O
  | Imported.nat_S n' => S (imported_to_nat n')
  end.

(* Prove to_from: to (from x) = x *)
Definition nat_to_from : forall x : Imported.nat,
    IsomorphismDefinitions.eq (nat_to_imported (imported_to_nat x)) x.
Proof.
  fix IH 1.
  intro x.
  destruct x as [|x'].
  - apply IsomorphismDefinitions.eq_refl.
  - simpl.
    apply f_equal.
    apply IH.
Defined.

(* Prove from_to: from (to x) = x *)
Definition nat_from_to : forall x : nat,
    IsomorphismDefinitions.eq (imported_to_nat (nat_to_imported x)) x.
Proof.
  fix IH 1.
  intro x.
  destruct x as [|x'].
  - apply IsomorphismDefinitions.eq_refl.
  - simpl.
    apply f_equal.
    apply IH.
Defined.

Instance nat_iso : Iso nat imported_nat :=
  {|
    to := nat_to_imported;
    from := imported_to_nat;
    to_from := nat_to_from;
    from_to := nat_from_to
  |}.

Instance: KnownConstant nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor nat nat_iso := {}.
Instance: IsoStatementProofBetween nat Imported.nat nat_iso := {}.
