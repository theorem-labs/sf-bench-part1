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

(* Aliases for compatibility *)
Definition imported_to_nat := nat_from_imported.

(* Round-trip lemmas as Logic.eq *)
Fixpoint nat_round_trip (x : nat) : @Logic.eq nat (nat_from_imported (nat_to_imported x)) x :=
  match x return @Logic.eq nat (nat_from_imported (nat_to_imported x)) x with
  | O => Logic.eq_refl
  | S n' => match nat_round_trip n' in (@Logic.eq _ _ y) return @Logic.eq nat (S (nat_from_imported (nat_to_imported n'))) (S y) with
            | Logic.eq_refl => Logic.eq_refl
            end
  end.

Fixpoint imported_round_trip (x : Imported.nat) : @Logic.eq Imported.nat (nat_to_imported (nat_from_imported x)) x :=
  match x return @Logic.eq Imported.nat (nat_to_imported (nat_from_imported x)) x with
  | Imported.nat_O => Logic.eq_refl
  | Imported.nat_S n' => match imported_round_trip n' in (@Logic.eq _ _ y) return @Logic.eq Imported.nat (Imported.nat_S (nat_to_imported (nat_from_imported n'))) (Imported.nat_S y) with
                         | Logic.eq_refl => Logic.eq_refl
                         end
  end.

Instance nat_iso : Iso nat imported_nat :=
  Build_Iso nat_to_imported nat_from_imported nat_to_from nat_from_to.

Instance: KnownConstant nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor nat nat_iso := {}.
Instance: IsoStatementProofBetween nat Imported.nat nat_iso := {}.