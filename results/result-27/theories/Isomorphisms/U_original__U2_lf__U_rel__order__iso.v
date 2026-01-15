From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
(* Typeclasses Opaque rel_iso. *) (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf__U_rel__relation__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf__U_rel__reflexive__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf__U_rel__transitive__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf__U_rel__antisymmetric__iso.

Definition imported_Original_LF_Rel_order : forall x : Type, (x -> x -> SProp) -> SProp := (@Imported.Original_LF_Rel_order).

(* Helper: isomorphism between Prop conjunction and Lean.And *)
Definition iso_and_Lean_And (P1 P2 : Prop) (S1 S2 : SProp) (h1 : Iso P1 S1) (h2 : Iso P2 S2) : Iso (P1 /\ P2) (Lean.And S1 S2).
Proof.
  unshelve eapply Build_Iso.
  - intro H. destruct H as [p1 p2].
    exact (Lean.And_intro S1 S2 (to h1 p1) (to h2 p2)).
  - intro H. split.
    + exact (from h1 (Lean.left S1 S2 H)).
    + exact (from h2 (Lean.right S1 S2 H)).
  - intro H. apply IsomorphismDefinitions.eq_refl.  (* SProp proof irrelevance *)
  - intro H. destruct H as [p1 p2].
    (* Use proof irrelevance for Prop conjunction *)
    pose proof (ProofIrrelevance.proof_irrelevance (P1 /\ P2)
      (conj (from h1 (Lean.left S1 S2 (Lean.And_intro S1 S2 (to h1 p1) (to h2 p2))))
            (from h2 (Lean.right S1 S2 (Lean.And_intro S1 S2 (to h1 p1) (to h2 p2)))))
      (conj p1 p2)) as Hirr.
    destruct Hirr.
    apply IsomorphismDefinitions.eq_refl.
Defined.

Instance Original_LF_Rel_order_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF.Rel.relation x1) (x4 : x2 -> x2 -> SProp),
  (forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> forall (x7 : x1) (x8 : x2), rel_iso hx x7 x8 -> Iso (x3 x5 x7) (x4 x6 x8)) -> Iso (Original.LF.Rel.order x3) (imported_Original_LF_Rel_order x4).
Proof.
  intros x1 x2 hx x3 x4 hrel.
  unfold Original.LF.Rel.order, imported_Original_LF_Rel_order, Imported.Original_LF_Rel_order.
  (* order x3 = reflexive x3 /\ antisymmetric x3 /\ transitive x3 *)
  (* Imported version = Lean.And (reflexive x4) (Lean.And (antisymmetric x4) (transitive x4)) *)
  
  (* Get isomorphisms for the components using @ to avoid implicit args issues *)
  pose proof (@Original_LF_Rel_reflexive_iso x1 x2 hx x3 x4 hrel) as Hrefl.
  pose proof (@Original_LF_Rel_antisymmetric_iso x1 x2 hx x3 x4 hrel) as Hanti.
  pose proof (@Original_LF_Rel_transitive_iso x1 x2 hx x3 x4 hrel) as Htrans.
  
  (* Build nested And isomorphism *)
  apply iso_and_Lean_And.
  - exact Hrefl.
  - apply iso_and_Lean_And.
    + exact Hanti.
    + exact Htrans.
Defined.

Instance: KnownConstant (@Original.LF.Rel.order) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Original_LF_Rel_order) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF.Rel.order) Original_LF_Rel_order_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF.Rel.order) (@Imported.Original_LF_Rel_order) Original_LF_Rel_order_iso := {}.