From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
From Stdlib Require Import ProofIrrelevance.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

Lemma leibniz_to_iso_eq_or : forall (A : Type) (a b : A), a = b -> IsomorphismDefinitions.eq a b.
Proof.
  intros A a b H. destruct H. apply IsomorphismDefinitions.eq_refl.
Qed.

Lemma prop_to_iso_eq_or : forall (P : Prop) (p1 p2 : P), IsomorphismDefinitions.eq p1 p2.
Proof.
  intros P p1 p2.
  apply leibniz_to_iso_eq_or.
  apply proof_irrelevance.
Qed.

Definition imported_or : SProp -> SProp -> SProp := Imported.or.

Instance or_iso : (forall (x1 : Prop) (x2 : SProp) (_ : Iso x1 x2) (x3 : Prop) (x4 : SProp) (_ : Iso x3 x4), Iso (or x1 x3) (imported_or x2 x4)).
Proof.
  intros x1 x2 Hx1 x3 x4 Hx3.
  unshelve eapply Build_Iso.
  - (* to: or x1 x3 -> imported_or x2 x4 *)
    intro H. destruct H as [a | b].
    { exact (Imported.or_inl x2 x4 (to Hx1 a)). }
    { exact (Imported.or_inr x2 x4 (to Hx3 b)). }
  - (* from: imported_or x2 x4 -> or x1 x3 *)
    (* Use sinhabitant to extract from SProp disjunction *)
    intro H.
    apply sinhabitant.
    (* Use the eliminator for Imported.or to build SInhabited (or x1 x3) *)
    exact (Imported.or_indl x2 x4 (fun _ => SInhabited (or x1 x3))
            (fun a => sinhabits (or_introl (from Hx1 a)))
            (fun b => sinhabits (or_intror (from Hx3 b)))
            H).
  - (* to_from *)
    intro x. apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro x. apply prop_to_iso_eq_or.
Defined.
Instance: KnownConstant or := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.or := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor or or_iso := {}.
Instance: IsoStatementProofBetween or Imported.or or_iso := {}.