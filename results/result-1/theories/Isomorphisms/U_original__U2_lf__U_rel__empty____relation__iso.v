From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
(* Typeclasses Opaque rel_iso. *) (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Definition imported_Original_LF_Rel_empty__relation : imported_nat -> imported_nat -> SProp := Imported.Original_LF_Rel_empty__relation.

(* Both empty_relation and Original_LF_Rel_empty__relation are empty inductives (no constructors).
   The isomorphism is straightforward because both are uninhabited. *)
Instance Original_LF_Rel_empty__relation_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 -> forall (x3 : nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> Iso (Original.LF.Rel.empty_relation x1 x3) (imported_Original_LF_Rel_empty__relation x2 x4).
Proof.
  intros x1 x2 H12 x3 x4 H34.
  refine {| 
    to := fun (H : Original.LF.Rel.empty_relation x1 x3) => 
            match H in Original.LF.Rel.empty_relation a b 
            return imported_Original_LF_Rel_empty__relation x2 x4 with end;
    from := fun (H : imported_Original_LF_Rel_empty__relation x2 x4) => 
            match H in Imported.Original_LF_Rel_empty__relation _ _
            return Original.LF.Rel.empty_relation x1 x3 with end;
    to_from := _;
    from_to := _
  |}.
  (* to_from: both types are empty, so destruct gives empty proof *)
  intro x; destruct x.
  (* from_to: both types are empty, so destruct gives empty proof *)
  intro x; destruct x.
Defined.
Instance: KnownConstant Original.LF.Rel.empty_relation := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF_Rel_empty__relation := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF.Rel.empty_relation Original_LF_Rel_empty__relation_iso := {}.
Instance: IsoStatementProofBetween Original.LF.Rel.empty_relation Imported.Original_LF_Rel_empty__relation Original_LF_Rel_empty__relation_iso := {}.