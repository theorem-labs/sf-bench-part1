From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
From Stdlib Require Import ProofIrrelevance.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

Lemma leibniz_to_iso_eq : forall (A : Type) (a b : A), a = b -> IsomorphismDefinitions.eq a b.
Proof.
  intros A a b H. destruct H. apply IsomorphismDefinitions.eq_refl.
Qed.

Lemma prop_to_iso_eq : forall (P : Prop) (p1 p2 : P), IsomorphismDefinitions.eq p1 p2.
Proof.
  intros P p1 p2.
  apply leibniz_to_iso_eq.
  apply proof_irrelevance.
Qed.

Definition imported_and : SProp -> SProp -> SProp := Imported.and.
Instance and_iso : (forall (x1 : Prop) (x2 : SProp) (_ : Iso x1 x2) (x3 : Prop) (x4 : SProp) (_ : Iso x3 x4), Iso (and x1 x3) (imported_and x2 x4)).
Proof.
  intros x1 x2 Hx1 x3 x4 Hx3.
  unshelve eapply Build_Iso.
  - (* to: and x1 x3 -> imported_and x2 x4 *)
    intro H. destruct H as [a b].
    exact (Imported.and_intro x2 x4 (to Hx1 a) (to Hx3 b)).
  - (* from: imported_and x2 x4 -> and x1 x3 *)
    intro H.
    exact (conj (from Hx1 (Imported.fst x2 x4 H)) 
                (from Hx3 (Imported.snd x2 x4 H))).
  - (* to_from *)
    intro x. apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro x. apply prop_to_iso_eq.
Defined.
Instance: KnownConstant and := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.and := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor and and_iso := {}.
Instance: IsoStatementProofBetween and Imported.and and_iso := {}.