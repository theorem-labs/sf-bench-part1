From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_and : SProp -> SProp -> SProp := Imported.and.
Instance and_iso : (forall (x1 : Prop) (x2 : SProp) (_ : Iso x1 x2) (x3 : Prop) (x4 : SProp) (_ : Iso x3 x4), Iso (Corelib.Init.Logic.and x1 x3) (imported_and x2 x4)).
Proof.
  intros x1 x2 H1 x3 x4 H2.
  unshelve eapply Build_Iso.
  - (* to: and x1 x3 -> imported_and x2 x4 *)
    intro p. destruct p as [a b].
    exact (Imported.and_intro x2 x4 (to H1 a) (to H2 b)).
  - (* from: imported_and x2 x4 -> and x1 x3 *)
    intro p. destruct p as [a b].
    exact (conj (from H1 a) (from H2 b)).
  - (* to_from *)
    intro p. destruct p as [a b].
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro p. destruct p as [a b].
    apply (IsoEq.f_equal2 (@conj x1 x3) (from_to H1 a) (from_to H2 b)).
Defined.
Instance: KnownConstant Corelib.Init.Logic.and := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.and := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Corelib.Init.Logic.and and_iso := {}.
Instance: IsoStatementProofBetween Corelib.Init.Logic.and Imported.and and_iso := {}.