From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_bool : Type := Imported.bool.

Definition bool_to_mybool (b : bool) : imported_bool :=
  match b with
  | true => Imported.Coq_bool_Coq_true
  | false => Imported.Coq_bool_Coq_false
  end.

Definition mybool_to_bool (b : imported_bool) : bool :=
  match b with
  | Imported.Coq_bool_Coq_true => true
  | Imported.Coq_bool_Coq_false => false
  end.

Instance bool_iso : Iso bool imported_bool.
Proof.
  refine {| to := bool_to_mybool; from := mybool_to_bool |}.
  - intro x. destruct x; apply IsomorphismDefinitions.eq_refl.
  - intro x. destruct x; apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant bool := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.bool := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor bool bool_iso := {}.
Instance: IsoStatementProofBetween bool Imported.bool bool_iso := {}.