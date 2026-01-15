From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf__U_rel__relation__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf__U_rel__reflexive__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf__U_rel__transitive__iso.
From IsomorphismChecker Require Export Isomorphisms.and__iso.

Monomorphic Definition imported_Original_LF_Rel_preorder : forall x : Type, (x -> x -> SProp) -> SProp := (@Imported.Original_LF_Rel_preorder).

Monomorphic Instance Original_LF_Rel_preorder_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF.Rel.relation x1) (x4 : x2 -> x2 -> SProp),
  (forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> forall (x7 : x1) (x8 : x2), rel_iso hx x7 x8 -> Iso (x3 x5 x7) (x4 x6 x8)) ->
  Iso (Original.LF.Rel.preorder x3) (imported_Original_LF_Rel_preorder x4).
Proof.
  intros x1 x2 hx x3 x4 Hrel.
  unfold Original.LF.Rel.preorder, imported_Original_LF_Rel_preorder, Imported.Original_LF_Rel_preorder.
  (* preorder = reflexive /\ transitive *)
  (* imported = and (reflexive) (transitive) *)
  pose proof (@Original_LF_Rel_reflexive_iso x1 x2 hx x3 x4 Hrel) as Hrefl.
  pose proof (@Original_LF_Rel_transitive_iso x1 x2 hx x3 x4 Hrel) as Htrans.
  (* and_iso expects: Iso x1 x2 -> Iso x3 x4 -> Iso (x1 /\ x3) (imported_and x2 x4) *)
  unfold imported_Original_LF_Rel_reflexive in Hrefl.
  unfold imported_Original_LF_Rel_transitive in Htrans.
  apply (@and_iso (Original.LF.Rel.reflexive x3) _ Hrefl (Original.LF.Rel.transitive x3) _ Htrans).
Defined.
Instance: KnownConstant (@Original.LF.Rel.preorder) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Original_LF_Rel_preorder) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF.Rel.preorder) Original_LF_Rel_preorder_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF.Rel.preorder) (@Imported.Original_LF_Rel_preorder) Original_LF_Rel_preorder_iso := {}.