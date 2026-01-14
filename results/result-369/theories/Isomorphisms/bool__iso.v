From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_bool : Type := Imported.bool.
Instance bool_iso : Iso bool imported_bool.
Proof.
  apply Build_Iso with
    (to := fun b => match b with true => Imported.bool_true | false => Imported.bool_false end)
    (from := fun b => match b with Imported.bool_true => true | Imported.bool_false => false end).
  - intros x. destruct x; apply IsomorphismDefinitions.eq_refl.
  - intros x. destruct x; apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant bool := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.bool := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor bool bool_iso := {}.
Instance: IsoStatementProofBetween bool Imported.bool bool_iso := {}.