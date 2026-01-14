From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_and : SProp -> SProp -> SProp := Imported.and.

Instance and_iso : (forall (x1 : Prop) (x2 : SProp) (_ : Iso x1 x2) (x3 : Prop) (x4 : SProp) (_ : Iso x3 x4), Iso (and x1 x3) (imported_and x2 x4)).
Proof.
  intros x1 x2 hx1 x3 x4 hx2.
  unshelve eapply Build_Iso.
  - (* to: and x1 x3 -> imported_and x2 x4 *)
    intro p.
    destruct p as [p1 p2].
    unfold imported_and, Imported.and.
    exact (Lean.And_intro _ _ (@to _ _ hx1 p1) (@to _ _ hx2 p2)).
  - (* from: imported_and x2 x4 -> and x1 x3 *)
    intro q.
    unfold imported_and, Imported.and in q.
    destruct q as [q1 q2].
    exact (conj (@from _ _ hx1 q1) (@from _ _ hx2 q2)).
  - (* to_from: forall q, eq (to (from q)) q *)
    intro q.
    (* Both sides are in SProp, so they are equal by eq_refl *)
    exact IsomorphismDefinitions.eq_refl.
  - (* from_to: forall p, eq (from (to p)) p *)
    intro p.
    destruct p as [p1 p2].
    (* We need to show: eq (conj (from (to p1)) (from (to p2))) (conj p1 p2) *)
    (* Use f_equal2 with the right types *)
    pose proof (@from_to _ _ hx1 p1) as H1.
    pose proof (@from_to _ _ hx2 p2) as H2.
    (* Both H1 and H2 are in SProp eq, we need to build the conjunction equality *)
    exact (f_equal2 (@conj x1 x3) H1 H2).
Defined.

Instance: KnownConstant and := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.and := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor and and_iso := {}.
Instance: IsoStatementProofBetween and Imported.and and_iso := {}.
