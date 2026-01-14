From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_bool : Type := Imported.Datatypes_bool.

Definition bool_to (b : Datatypes.bool) : Imported.Datatypes_bool :=
  match b with
  | Datatypes.true => Imported.Datatypes_bool_true
  | Datatypes.false => Imported.Datatypes_bool_false
  end.

Definition bool_from (b : Imported.Datatypes_bool) : Datatypes.bool :=
  match b with
  | Imported.Datatypes_bool_true => Datatypes.true
  | Imported.Datatypes_bool_false => Datatypes.false
  end.

Lemma bool_to_from : forall b, IsomorphismDefinitions.eq (bool_to (bool_from b)) b.
Proof.
  intros []; apply IsomorphismDefinitions.eq_refl.
Defined.

Lemma bool_from_to : forall b, IsomorphismDefinitions.eq (bool_from (bool_to b)) b.
Proof.
  intros []; apply IsomorphismDefinitions.eq_refl.
Defined.

Instance bool_iso : Iso Datatypes.bool imported_bool :=
  Build_Iso bool_to bool_from bool_to_from bool_from_to.

Instance: KnownConstant Datatypes.bool := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Datatypes_bool := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Datatypes.bool bool_iso := {}.
Instance: IsoStatementProofBetween Datatypes.bool Imported.Datatypes_bool bool_iso := {}.