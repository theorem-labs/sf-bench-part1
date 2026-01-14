From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.option__iso.

Definition imported_None : forall x : Type, imported_option x := (@Imported.None).
Instance None_iso : forall (x1 x2 : Type) (hx : Iso x1 x2), rel_iso (option_iso hx) None (imported_None x2).
Proof.
  intros x1 x2 hx.
  unfold rel_iso, option_iso. simpl.
  unfold option_to_imported.
  unfold imported_None, Imported.None.
  exact IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant (@None) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.None) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@None) None_iso := {}.
Instance: IsoStatementProofBetween (@None) (@Imported.None) None_iso := {}.