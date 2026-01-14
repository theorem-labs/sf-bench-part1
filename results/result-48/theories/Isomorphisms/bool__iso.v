From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_bool : Type := Imported.bool.

(* Convert from Rocq bool to Imported.bool *)
Definition bool_to_imported (b : Datatypes.bool) : imported_bool :=
  match b with
  | true => Imported.bool_mytrue
  | false => Imported.bool_myfalse
  end.

(* Convert from Imported.bool to Rocq bool *)
Definition imported_to_bool (b : imported_bool) : Datatypes.bool :=
  match b with
  | Imported.bool_mytrue => true
  | Imported.bool_myfalse => false
  end.

(* Proof that to_from holds *)
Lemma bool_to_from : forall x : imported_bool, 
  IsomorphismDefinitions.eq (bool_to_imported (imported_to_bool x)) x.
Proof.
  intro x.
  destruct x; apply IsomorphismDefinitions.eq_refl.
Qed.

(* Proof that from_to holds *)
Lemma bool_from_to : forall x : Datatypes.bool,
  IsomorphismDefinitions.eq (imported_to_bool (bool_to_imported x)) x.
Proof.
  intro x. destruct x; apply IsomorphismDefinitions.eq_refl.
Qed.

Instance bool_iso : Iso Datatypes.bool imported_bool := {|
  to := bool_to_imported;
  from := imported_to_bool;
  to_from := bool_to_from;
  from_to := bool_from_to
|}.

Instance: KnownConstant Datatypes.bool := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.bool := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Datatypes.bool bool_iso := {}.
Instance: IsoStatementProofBetween Datatypes.bool Imported.bool bool_iso := {}.