From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_bool : Type := Imported.Coq_bool.

Definition bool_to (b : bool) : imported_bool :=
  match b with
  | true => Imported.Coq_bool_Coq_true
  | false => Imported.Coq_bool_Coq_false
  end.

Definition bool_from (b : imported_bool) : bool :=
  match b with
  | Imported.Coq_bool_Coq_true => true
  | Imported.Coq_bool_Coq_false => false
  end.

Lemma bool_to_from : forall x, IsomorphismDefinitions.eq (bool_to (bool_from x)) x.
Proof.
  intros x. destruct x; apply IsomorphismDefinitions.eq_refl.
Qed.

Lemma bool_from_to : forall x, IsomorphismDefinitions.eq (bool_from (bool_to x)) x.
Proof.
  intros x. destruct x; apply IsomorphismDefinitions.eq_refl.
Qed.

Instance bool_iso : Iso bool imported_bool := {|
  to := bool_to;
  from := bool_from;
  to_from := bool_to_from;
  from_to := bool_from_to
|}.
Instance: KnownConstant bool := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Coq_bool := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor bool bool_iso := {}.
Instance: IsoStatementProofBetween bool Imported.Coq_bool bool_iso := {}.