From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.

Definition imported_iff : SProp -> SProp -> SProp := Imported.iff.

From Stdlib Require Import ProofIrrelevance.

(* Build an Iso between (x1 <-> x3) and (imported_iff x2 x4) *)
(* imported_iff x2 x4 = Imported.iff x2 x4 which is a record with mp/mpr *)
Instance iff_iso : forall (x1 : Prop) (x2 : SProp), Iso x1 x2 -> forall (x3 : Prop) (x4 : SProp), Iso x3 x4 -> Iso (x1 <-> x3) (imported_iff x2 x4).
Proof.
  intros x1 x2 hx x3 x4 hx0.
  unshelve econstructor.
  - (* to : (x1 <-> x3) -> imported_iff x2 x4 *)
    intros [H1 H2].
    exact (Imported.iff_intro x2 x4 (fun a => hx0.(to) (H1 (hx.(from) a))) (fun b => hx.(to) (H2 (hx0.(from) b)))).
  - (* from : imported_iff x2 x4 -> (x1 <-> x3) *)
    intros H.
    split.
    + intros a. exact (hx0.(from) (Imported.mp x2 x4 H (hx.(to) a))).
    + intros b. exact (hx.(from) (Imported.mpr x2 x4 H (hx0.(to) b))).
  - (* to_from *)
    intros x.
    (* Since imported_iff is in SProp, this is trivial by proof irrelevance *)
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intros x.
    (* x1 <-> x3 is in Prop, so we use proof_irrelevance *)
    destruct x as [H1 H2].
    assert (H1' : forall (p q : x1 <-> x3), IsomorphismDefinitions.eq p q).
    { intros p q.
      assert (Heq : p = q) by (apply proof_irrelevance).
      rewrite Heq. apply IsomorphismDefinitions.eq_refl. }
    apply H1'.
Defined.
Instance: KnownConstant iff := {}.
Instance: KnownConstant Imported.iff := {}.
Instance: IsoStatementProofFor iff iff_iso := {}.
Instance: IsoStatementProofBetween iff Imported.iff iff_iso := {}.