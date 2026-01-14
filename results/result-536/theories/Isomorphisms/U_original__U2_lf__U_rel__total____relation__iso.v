From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Definition imported_Original_LF_Rel_total__relation : imported_nat -> imported_nat -> SProp := Imported.Original_LF_Rel_total__relation.
Instance Original_LF_Rel_total__relation_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 -> forall (x3 : nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> Iso (Original.LF.Rel.total_relation x1 x3) (imported_Original_LF_Rel_total__relation x2 x4).
Proof.
  intros x1 x2 H12 x3 x4 H34.
  (* both sides are empty propositions (no constructors) *)
  refine {| to := (fun h : Original.LF.Rel.total_relation x1 x3 => match h with end)
          ; from := (fun h : imported_Original_LF_Rel_total__relation x2 x4 => match h with end)
          ; to_from := _
          ; from_to := _ |}.
  - intro h. destruct h.
  - intro h. destruct h.
Qed.
Instance: KnownConstant Original.LF.Rel.total_relation := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF_Rel_total__relation := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF.Rel.total_relation Original_LF_Rel_total__relation_iso := {}.
Instance: IsoStatementProofBetween Original.LF.Rel.total_relation Imported.Original_LF_Rel_total__relation Original_LF_Rel_total__relation_iso := {}.