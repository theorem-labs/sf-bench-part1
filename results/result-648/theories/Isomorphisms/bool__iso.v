From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_bool : Type := Imported.bool.

Definition bool_to_imported (b : bool) : imported_bool :=
  match b with
  | true => Imported.bool_true
  | false => Imported.bool_false
  end.

Definition imported_to_bool (b : imported_bool) : bool :=
  match b with
  | Imported.bool_true => true
  | Imported.bool_false => false
  end.

Instance bool_iso : Iso bool imported_bool.
Proof.
  unshelve eapply Build_Iso.
  - exact bool_to_imported.
  - exact imported_to_bool.
  - intro b. destruct b; simpl; apply IsomorphismDefinitions.eq_refl.
  - intro b. destruct b; simpl; apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant bool := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.bool := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor bool bool_iso := {}.
Instance: IsoStatementProofBetween bool Imported.bool bool_iso := {}.