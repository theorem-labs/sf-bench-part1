From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


(* We use Bool' from Imported *)
Definition imported_bool : Type := Imported.Bool'.

(* Conversion functions *)
Definition bool_to_imported (b : Datatypes.bool) : Imported.Bool' :=
  match b with
  | true => Imported.Bool'_true
  | false => Imported.Bool'_false
  end.

Definition bool_from_imported (b : Imported.Bool') : Datatypes.bool :=
  match b with
  | Imported.Bool'_true => true
  | Imported.Bool'_false => false
  end.

Lemma bool_to_from : forall b, bool_to_imported (bool_from_imported b) = b.
Proof. destruct b; reflexivity. Qed.

Lemma bool_from_to : forall b, bool_from_imported (bool_to_imported b) = b.
Proof. destruct b; reflexivity. Qed.

(* Convert from Logic.eq to IsomorphismDefinitions.eq *)
Lemma logic_eq_to_iso_eq : forall (A : Type) (x y : A), @Logic.eq A x y -> IsomorphismDefinitions.eq x y.
Proof.
  intros A x y H. destruct H. apply IsomorphismDefinitions.eq_refl.
Qed.

Instance bool_iso : Iso Datatypes.bool imported_bool := {|
  to := bool_to_imported;
  from := bool_from_imported;
  to_from := fun x => logic_eq_to_iso_eq (bool_to_from x);
  from_to := fun x => logic_eq_to_iso_eq (bool_from_to x);
|}.

Instance: KnownConstant Datatypes.bool := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Bool' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Datatypes.bool bool_iso := {}.
Instance: IsoStatementProofBetween Datatypes.bool Imported.Bool' bool_iso := {}.