From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
From Stdlib Require Import ProofIrrelevance.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_or : SProp -> SProp -> SProp := Imported.or.

(* Helper lemma to convert between Coq eq and SProp eq for Prop types *)
Lemma prop_proof_irrelevance_sprop : forall (P : Prop) (x y : P), IsomorphismDefinitions.eq x y.
Proof.
  intros P x y.
  assert (x = y) by apply proof_irrelevance.
  subst. apply IsomorphismDefinitions.eq_refl.
Defined.

(* Build the Iso manually using SInhabited to handle SProp elimination *)
Instance or_iso : (forall (x1 : Prop) (x2 : SProp) (_ : Iso x1 x2) (x3 : Prop) (x4 : SProp) (_ : Iso x3 x4), Iso (or x1 x3) (imported_or x2 x4)).
Proof.
  intros x1 x2 iso12 x3 x4 iso34.
  unfold imported_or.
  unshelve econstructor.
  - (* to: or x1 x3 -> Imported.or x2 x4 *)
    intros [Hp | Hq].
    + apply Imported.or_inl. apply iso12.(to). exact Hp.
    + apply Imported.or_inr. apply iso34.(to). exact Hq.
  - (* from: Imported.or x2 x4 -> or x1 x3 *)
    (* We need to use sinhabitant to extract from SProp *)
    intro H.
    (* Use the indl eliminator which targets SProp, then use sinhabitant *)
    apply sinhabitant.
    apply (Imported.or_indl x2 x4 (fun _ => SInhabited (or x1 x3))).
    + intro hp. apply sinhabits. left. apply iso12.(from). exact hp.
    + intro hq. apply sinhabits. right. apply iso34.(from). exact hq.
    + exact H.
  - (* to_from: in SProp, proof irrelevance is automatic *)
    intros x.
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to: need proof irrelevance since or is in Prop *)
    intros x.
    apply prop_proof_irrelevance_sprop.
Defined.

Instance: KnownConstant or := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.or := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor or or_iso := {}.
Instance: IsoStatementProofBetween or Imported.or or_iso := {}.