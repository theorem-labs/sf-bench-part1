From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

(* Imported.bool is an alias for Imported.Rocq_Bool which has constructors Rocq_Bool_true and Rocq_Bool_false *)
Definition imported_bool : Type := Imported.bool.

Definition bool_to_imported (b : bool) : Imported.bool :=
  match b with
  | true => Imported.Rocq_Bool_true
  | false => Imported.Rocq_Bool_false
  end.

Definition imported_to_bool (b : Imported.bool) : bool :=
  match b with
  | Imported.Rocq_Bool_true => true
  | Imported.Rocq_Bool_false => false
  end.

Lemma bool_roundtrip : forall b, IsomorphismDefinitions.eq (imported_to_bool (bool_to_imported b)) b.
Proof. destruct b; exact IsomorphismDefinitions.eq_refl. Qed.

Lemma imported_bool_roundtrip : forall b, IsomorphismDefinitions.eq (bool_to_imported (imported_to_bool b)) b.
Proof. destruct b; exact IsomorphismDefinitions.eq_refl. Qed.

Instance bool_iso : Iso bool imported_bool :=
  Build_Iso bool_to_imported imported_to_bool imported_bool_roundtrip bool_roundtrip.

Instance: KnownConstant bool := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.bool := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor bool bool_iso := {}.
Instance: IsoStatementProofBetween bool Imported.bool bool_iso := {}.
