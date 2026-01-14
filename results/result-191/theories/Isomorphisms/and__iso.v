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
  unshelve refine (Build_Iso _ _ _ _).
  - (* to: and x1 x3 -> imported_and x2 x4 *)
    intro p. destruct p as [p1 p2]. 
    exact (Imported.and_conj _ _ (@to x1 x2 hx1 p1) (@to x3 x4 hx2 p2)).
  - (* from: imported_and x2 x4 -> and x1 x3 *)
    intro q. destruct q as [q1 q2]. 
    exact (conj (@from x1 x2 hx1 q1) (@from x3 x4 hx2 q2)).
  - (* to_from: SProp so trivial *)
    intro q. apply IsomorphismDefinitions.eq_refl.
  - (* from_to: Prop equality, use proof irrelevance *)
    intro p. 
    apply seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.
Instance: KnownConstant and := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.and := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor and and_iso := {}.
Instance: IsoStatementProofBetween and Imported.and and_iso := {}.