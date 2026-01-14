From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_bool : Type := Imported.Bool.

Definition bool_to : bool -> imported_bool :=
  fun b => match b with
           | true => Imported.Bool_true
           | false => Imported.Bool_false
           end.

Definition bool_from : imported_bool -> bool :=
  fun b => match b with
           | Imported.Bool_true => true
           | Imported.Bool_false => false
           end.

Lemma bool_to_from : forall x, IsomorphismDefinitions.eq (bool_to (bool_from x)) x.
Proof. intros []; apply IsomorphismDefinitions.eq_refl. Defined.

Lemma bool_from_to : forall x, IsomorphismDefinitions.eq (bool_from (bool_to x)) x.
Proof. intros []; apply IsomorphismDefinitions.eq_refl. Defined.

Instance bool_iso : Iso bool imported_bool :=
  Build_Iso bool_to bool_from bool_to_from bool_from_to.

Instance: KnownConstant bool := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Bool := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor bool bool_iso := {}.
Instance: IsoStatementProofBetween bool Imported.Bool bool_iso := {}.