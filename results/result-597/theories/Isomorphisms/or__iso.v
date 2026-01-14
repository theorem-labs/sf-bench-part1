From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_or : SProp -> SProp -> SProp := Imported.or.

Instance or_iso : (forall (x1 : Prop) (x2 : SProp) (_ : Iso x1 x2) (x3 : Prop) (x4 : SProp) (_ : Iso x3 x4), Iso (or x1 x3) (imported_or x2 x4)).
Proof.
  intros x1 x2 H12 x3 x4 H34.
  unshelve eapply Build_Iso.
  - (* to: or x1 x3 -> imported_or x2 x4 *)
    intro Ho.
    destruct Ho as [Ha | Hb].
    + exact (Imported.or_intro x2 x4 (fun C fa fb => fa (to H12 Ha))).
    + exact (Imported.or_intro x2 x4 (fun C fa fb => fb (to H34 Hb))).
  - (* from: imported_or x2 x4 -> or x1 x3 *)
    intro Hi.
    destruct Hi as [elim_f].
    (* Use the eliminator at SInhabited (or x1 x3) *)
    pose (result := elim_f (SInhabited (or x1 x3))
                           (fun h2 => sinhabits (or_introl (from H12 h2)))
                           (fun h4 => sinhabits (or_intror (from H34 h4)))).
    exact (sinhabitant result).
  - (* to_from *)
    intro Hi.
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro Ho.
    (* Use proof irrelevance for Prop *)
    apply seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant or := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.or := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor or or_iso := {}.
Instance: IsoStatementProofBetween or Imported.or or_iso := {}.