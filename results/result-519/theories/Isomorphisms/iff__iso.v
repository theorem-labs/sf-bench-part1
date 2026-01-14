From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_iff : SProp -> SProp -> SProp := Imported.iff.

(* Helper to convert standard eq to IsomorphismDefinitions.eq *)
Definition prop_eq_to_iso_eq {A : Type} {x y : A} (H : x = y) : IsomorphismDefinitions.eq x y :=
  match H with
  | Logic.eq_refl => IsomorphismDefinitions.eq_refl x
  end.

(* Imported.iff is defined as And (P -> Q) (Q -> P) where And is the Lean.And record *)
(* We need to prove an isomorphism between Prop iff and SProp iff *)
Instance iff_iso : forall (x1 : Prop) (x2 : SProp), Iso x1 x2 -> forall (x3 : Prop) (x4 : SProp), Iso x3 x4 -> Iso (x1 <-> x3) (imported_iff x2 x4).
Proof.
  intros x1 x2 Hx1 x3 x4 Hx3.
  unfold imported_iff, Imported.iff.
  (* Goal: Iso (x1 <-> x3) (Lean.And (x2 -> x4) (x4 -> x2)) *)
  unshelve eapply Build_Iso.
  - (* to: (x1 <-> x3) -> Lean.And (x2 -> x4) (x4 -> x2) *)
    intro H. destruct H as [H1 H2].
    split.
    + intro h2. apply (to Hx3). apply H1. apply (from Hx1). exact h2.
    + intro h4. apply (to Hx1). apply H2. apply (from Hx3). exact h4.
  - (* from: Lean.And (x2 -> x4) (x4 -> x2) -> (x1 <-> x3) *)
    intro H. destruct H as [H1 H2].
    split.
    + intro h1. apply (from Hx3). apply H1. apply (to Hx1). exact h1.
    + intro h3. apply (from Hx1). apply H2. apply (to Hx3). exact h3.
  - (* to_from *)
    intro x. exact (IsomorphismDefinitions.eq_refl _).
  - (* from_to *)
    intro x.
    (* Use proof irrelevance for Prop iff, then convert to SProp eq *)
    apply prop_eq_to_iso_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant iff := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.iff := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor iff iff_iso := {}.
Instance: IsoStatementProofBetween iff Imported.iff iff_iso := {}.