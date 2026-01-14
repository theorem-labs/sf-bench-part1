From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_nat : Type := Imported.nat.

(* Define the to and from functions for nat isomorphism *)
Fixpoint nat_to_imported (n : nat) : Imported.nat :=
  match n with
  | O => Imported.nat_O
  | S n' => Imported.nat_S (nat_to_imported n')
  end.

Fixpoint nat_from_imported (n : Imported.nat) : nat :=
  match n with
  | Imported.nat_O => O
  | Imported.nat_S n' => S (nat_from_imported n')
  end.

Lemma nat_to_from : forall x : Imported.nat, IsomorphismDefinitions.eq (nat_to_imported (nat_from_imported x)) x.
Proof.
  fix IH 1.
  intros x.
  destruct x as [|n'].
  - apply IsomorphismDefinitions.eq_refl.
  - simpl. apply (IsoEq.f_equal Imported.nat_S (IH n')).
Defined.

Lemma nat_from_to : forall x : nat, IsomorphismDefinitions.eq (nat_from_imported (nat_to_imported x)) x.
Proof.
  fix IH 1.
  intros x.
  destruct x as [|n'].
  - apply IsomorphismDefinitions.eq_refl.
  - simpl. apply (IsoEq.f_equal S (IH n')).
Defined.

(* Alias for nat_from_imported *)
Definition imported_to_nat := nat_from_imported.

(* Round trip lemma *)
Fixpoint nat_round_trip (x : nat) : @Logic.eq nat (imported_to_nat (nat_to_imported x)) x :=
  match x with
  | O => Logic.eq_refl
  | S n' => match nat_round_trip n' in (@Logic.eq _ _ z) return @Logic.eq nat (S (imported_to_nat (nat_to_imported n'))) (S z) with
            | Logic.eq_refl => Logic.eq_refl
            end
  end.

Instance nat_iso : Iso nat imported_nat :=
  Build_Iso nat_to_imported nat_from_imported nat_to_from nat_from_to.

Instance: KnownConstant nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor nat nat_iso := {}.
Instance: IsoStatementProofBetween nat Imported.nat nat_iso := {}.