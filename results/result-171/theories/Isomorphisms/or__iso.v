From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
From Stdlib Require Import ProofIrrelevance.
From Stdlib Require Import Classical_Prop.
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

(* sFalse: an empty SProp that can be eliminated to any type *)
Inductive sFalse : SProp := .

Lemma sFalse_elim : forall P : Prop, sFalse -> P.
Proof.
  intros P H. destruct H.
Qed.

Definition imported_or : SProp -> SProp -> SProp := Imported.or.

(* Helper to extract from Imported.or using the isomorphisms *)
(* Key insight: if Imported.or x2 x4 is inhabited and we have Iso x1 x2 and Iso x3 x4,
   then we can use classical logic to find which of x1 or x3 is true.
   If imported_or x2 x4 holds, then either x2 or x4 is inhabited.
   Since from Hx1 : x2 -> x1 and from Hx3 : x4 -> x3, we can try classical reasoning. *)

Instance or_iso : (forall (x1 : Prop) (x2 : SProp) (_ : Iso x1 x2) (x3 : Prop) (x4 : SProp) (_ : Iso x3 x4), Iso (or x1 x3) (imported_or x2 x4)).
Proof.
  intros x1 x2 Hx1 x3 x4 Hx3.
  unshelve eapply Build_Iso.
  - (* to: or x1 x3 -> imported_or x2 x4 *)
    intro H. destruct H as [a | b].
    { exact (Imported.or_inl x2 x4 (to Hx1 a)). }
    { exact (Imported.or_inr x2 x4 (to Hx3 b)). }
  - (* from: imported_or x2 x4 -> or x1 x3 *)
    (* We can't destruct imported_or since it's SProp. Use classical logic. *)
    intro H.
    destruct (classic x1) as [Hx1_true | Hx1_false].
    { left. exact Hx1_true. }
    { destruct (classic x3) as [Hx3_true | Hx3_false].
      { right. exact Hx3_true. }
      { (* Both x1 and x3 are false. But imported_or x2 x4 is inhabited.
           This means either x2 or x4 is inhabited. Using from Hx1 or from Hx3,
           we'd get x1 or x3 inhabited, contradiction.
           We can use Imported.or_indl which eliminates to SProp (sFalse). *)
        apply sFalse_elim.
        (* Use the eliminator to produce sFalse *)
        exact (Imported.or_indl x2 x4 (fun _ => sFalse)
                (fun a => match Hx1_false (from Hx1 a) with end)
                (fun b => match Hx3_false (from Hx3 b) with end)
                H).
      }
    }
  - (* to_from *)
    intro x. apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro x. apply prop_to_iso_eq.
Defined.
Instance: KnownConstant or := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.or := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor or or_iso := {}.
Instance: IsoStatementProofBetween or Imported.or or_iso := {}.