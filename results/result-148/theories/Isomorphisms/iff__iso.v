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

Definition imported_iff : SProp -> SProp -> SProp := Imported.iff.

(* iff x1 x3 = (x1 -> x3) /\ (x3 -> x1) *)
(* imported_iff x2 x4 = Imported.and (x2 -> x4) (x4 -> x2) *)

Instance iff_iso : forall (x1 : Prop) (x2 : SProp), Iso x1 x2 -> forall (x3 : Prop) (x4 : SProp), Iso x3 x4 -> Iso (x1 <-> x3) (imported_iff x2 x4).
Proof.
  intros x1 x2 Hx1 x3 x4 Hx3.
  unfold imported_iff, Imported.iff.
  (* Now we need Iso (x1 <-> x3) (Imported.and (x2 -> x4) (x4 -> x2)) *)
  (* x1 <-> x3 is (x1 -> x3) /\ (x3 -> x1) *)
  unshelve eapply Build_Iso.
  - (* to: (x1 <-> x3) -> Imported.and (x2 -> x4) (x4 -> x2) *)
    intro H. destruct H as [H1 H3].
    apply Imported.and_intro.
    + intro a. exact (to Hx3 (H1 (from Hx1 a))).
    + intro b. exact (to Hx1 (H3 (from Hx3 b))).
  - (* from: Imported.and (x2 -> x4) (x4 -> x2) -> (x1 <-> x3) *)
    intro H.
    split.
    + intro a. exact (from Hx3 (Imported.fst _ _ H (to Hx1 a))).
    + intro b. exact (from Hx1 (Imported.snd _ _ H (to Hx3 b))).
  - (* to_from *)
    intro x. apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro x. apply prop_to_iso_eq.
Defined.
Instance: KnownConstant iff := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.iff := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor iff iff_iso := {}.
Instance: IsoStatementProofBetween iff Imported.iff iff_iso := {}.