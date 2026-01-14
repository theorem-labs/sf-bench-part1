From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

(* bool in Imported is defined as mybool *)
Definition imported_bool : Type := Imported.bool.

Definition bool_to_imported (b : bool) : Imported.bool :=
  match b with
  | true => Imported.mybool_mytrue
  | false => Imported.mybool_myfalse
  end.

Definition imported_to_bool (b : Imported.bool) : bool :=
  match b with
  | Imported.mybool_mytrue => true
  | Imported.mybool_myfalse => false
  end.

Lemma bool_roundtrip1 : forall b, bool_to_imported (imported_to_bool b) = b.
Proof. intros []; reflexivity. Qed.

Lemma bool_roundtrip2 : forall b, imported_to_bool (bool_to_imported b) = b.
Proof. intros []; reflexivity. Qed.

Instance bool_iso : Iso bool imported_bool.
Proof.
  exact (Build_Iso bool_to_imported imported_to_bool
    (fun b => seq_of_eq (bool_roundtrip1 b))
    (fun b => seq_of_eq (bool_roundtrip2 b))).
Defined.
Instance: KnownConstant bool := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.bool := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor bool bool_iso := {}.
Instance: IsoStatementProofBetween bool Imported.bool bool_iso := {}.