From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_True : SProp := Imported.True.

Instance True_iso : (Iso Logic.True imported_True).
Proof.
  refine (Build_Iso (fun _ => Imported.True_intro) (fun _ => Logic.I) _ _).
  - (* to_from: for all q : Imported.True, eq (to (from q)) q *)
    (* Since Imported.True is SProp, all its elements are definitionally equal *)
    intro q. exact IsomorphismDefinitions.eq_refl.
  - (* from_to: for all p : Logic.True, eq (from (to p)) p *)
    intro p. destruct p. exact IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Logic.True := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.True := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Logic.True True_iso := {}.
Instance: IsoStatementProofBetween Logic.True Imported.True True_iso := {}.
