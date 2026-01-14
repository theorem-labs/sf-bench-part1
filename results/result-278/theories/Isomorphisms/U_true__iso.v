From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_True : SProp := Imported.True.

(* Rocq's True is in Prop, Imported.True is in SProp. We need an isomorphism. *)
(* Since both are unit types, they are isomorphic via trivial maps *)
Instance True_iso : (Iso True imported_True).
Proof.
  refine {| to := fun _ => Imported.True_intro;
            from := fun _ => I;
            to_from := _;
            from_to := _ |}.
  - intro x. destruct x. apply IsomorphismDefinitions.eq_refl.
  - intro x. destruct x. apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant True := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.True := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor True True_iso := {}.
Instance: IsoStatementProofBetween True Imported.True True_iso := {}.