From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_True : SProp := Imported.True.

(* For to_from: we need IsomorphismDefinitions.eq (Imported.True_intro) t 
   Since Imported.True is SProp, all proofs are equal in SProp *)
Lemma True_to_from : forall t : Imported.True, IsomorphismDefinitions.eq Imported.True_intro t.
Proof.
  intro t. exact IsomorphismDefinitions.eq_refl.
Qed.

Instance True_iso : (Iso True imported_True) := {|
  to := fun _ => Imported.True_intro;
  from := fun _ => Logic.I;
  to_from := True_to_from;
  from_to := fun x => match x with Logic.I => IsomorphismDefinitions.eq_refl end
|}.
Instance: KnownConstant True := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.True := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor True True_iso := {}.
Instance: IsoStatementProofBetween True Imported.True True_iso := {}.