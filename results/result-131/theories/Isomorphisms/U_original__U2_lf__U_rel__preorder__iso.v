From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf__U_rel__relation__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf__U_rel__reflexive__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf__U_rel__transitive__iso.

Definition imported_Original_LF_Rel_preorder : forall x : Type, (x -> x -> SProp) -> SProp := (@Imported.Original_LF_Rel_preorder).

(* Helper: Iso between Prop /\ and SProp And when components are isomorphic *)
Definition iso_and_And {P1 P2 : Prop} {Q1 Q2 : SProp}
  (h1 : Iso P1 Q1) (h2 : Iso P2 Q2) : Iso (P1 /\ P2) (Lean.And Q1 Q2).
Proof.
  destruct h1 as [to1 from1 to_from1 from_to1].
  destruct h2 as [to2 from2 to_from2 from_to2].
  refine (@Build_Iso (P1 /\ P2) (Lean.And Q1 Q2)
      (fun pq => @Lean.And_intro Q1 Q2 (to1 (proj1 pq)) (to2 (proj2 pq)))
      (fun ab => conj (from1 (@Lean.left Q1 Q2 ab)) (from2 (@Lean.right Q1 Q2 ab)))
      _ _).
  - intro x. apply IsomorphismDefinitions.eq_refl.
  - intro x.
    (* P1 /\ P2 is a Prop, so we need proof irrelevance *)
    apply seq_of_peq_t.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance Original_LF_Rel_preorder_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF.Rel.relation x1) (x4 : x2 -> x2 -> SProp),
  (forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> forall (x7 : x1) (x8 : x2), rel_iso hx x7 x8 -> Iso (x3 x5 x7) (x4 x6 x8)) ->
  Iso (Original.LF.Rel.preorder x3) (imported_Original_LF_Rel_preorder x4).
Proof.
  intros x1 x2 hx x3 x4 hR.
  unfold Original.LF.Rel.preorder, imported_Original_LF_Rel_preorder.
  unfold Imported.Original_LF_Rel_preorder.
  set (iso_ref := @Original_LF_Rel_reflexive_iso x1 x2 hx x3 x4 hR).
  set (iso_tra := @Original_LF_Rel_transitive_iso x1 x2 hx x3 x4 hR).
  exact (iso_and_And iso_ref iso_tra).
Defined.

Instance: KnownConstant (@Original.LF.Rel.preorder) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Original_LF_Rel_preorder) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF.Rel.preorder) Original_LF_Rel_preorder_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF.Rel.preorder) (@Imported.Original_LF_Rel_preorder) Original_LF_Rel_preorder_iso := {}.