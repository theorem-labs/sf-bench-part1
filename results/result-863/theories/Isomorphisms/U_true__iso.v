From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso. (* for speed *)

Definition imported_True : SProp := Imported.True_.

Instance True_iso : (Iso True imported_True).
Proof.
  exists (fun _ => Imported.True__I) (fun _ => I).
  - intro x. destruct x. apply IsomorphismDefinitions.eq_refl.
  - intro x. destruct x. apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant True := {}.
Instance: KnownConstant Imported.True_ := {}.
Instance: IsoStatementProofFor True True_iso := {}.
Instance: IsoStatementProofBetween True Imported.True_ True_iso := {}.