From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_iff : SProp -> SProp -> SProp := Imported.iff.

Instance iff_iso : forall (x1 : Prop) (x2 : SProp), Iso x1 x2 -> forall (x3 : Prop) (x4 : SProp), Iso x3 x4 -> Iso (x1 <-> x3) (imported_iff x2 x4).
Proof.
  intros x1 x2 H1 x3 x4 H2.
  unfold iff, imported_iff, Imported.iff.
  (* iff x1 x3 = (x1 -> x3) /\ (x3 -> x1) *)
  (* imported_iff x2 x4 = Imported.and (x2 -> x4) (x4 -> x2) *)
  unshelve eapply Build_Iso.
  - (* to: (x1 <-> x3) -> Imported.and (x2 -> x4) (x4 -> x2) *)
    intro p. destruct p as [f g].
    apply (Imported.and_intro (x2 -> x4) (x4 -> x2)).
    + intro y. exact (to H2 (f (from H1 y))).
    + intro y. exact (to H1 (g (from H2 y))).
  - (* from: Imported.and (x2 -> x4) (x4 -> x2) -> (x1 <-> x3) *)
    intro p. destruct p as [f g].
    split.
    + intro y. exact (from H2 (f (to H1 y))).
    + intro y. exact (from H1 (g (to H2 y))).
  - (* to_from *)
    intro p. destruct p as [f g].
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro p. destruct p as [f g].
    (* Both sides are in (x1 <-> x3) which is a Prop, use proof irrelevance *)
    set (lhs := conj (fun y : x1 => from H2 (Imported.fst (x2 -> x4) (x4 -> x2) 
                   (Imported.and_intro (x2 -> x4) (x4 -> x2) 
                     (fun y0 : x2 => to H2 (f (from H1 y0)))
                     (fun y0 : x4 => to H1 (g (from H2 y0)))) (to H1 y)))
                     (fun y : x3 => from H1 (Imported.snd (x2 -> x4) (x4 -> x2)
                   (Imported.and_intro (x2 -> x4) (x4 -> x2) 
                     (fun y0 : x2 => to H2 (f (from H1 y0)))
                     (fun y0 : x4 => to H1 (g (from H2 y0)))) (to H2 y)))).
    pose proof (Stdlib.Logic.ProofIrrelevance.proof_irrelevance (iff x1 x3) lhs (conj f g)) as PIrr.
    exact (match PIrr in (_ = r) return (IsomorphismDefinitions.eq lhs r) with
           | Logic.eq_refl => IsomorphismDefinitions.eq_refl
           end).
Defined.
Instance: KnownConstant Logic.iff := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.iff := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Logic.iff iff_iso := {}.
Instance: IsoStatementProofBetween Logic.iff Imported.iff iff_iso := {}.