From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso. (* for speed *)

(* Imported.True is in SProp *)
Definition imported_True : SProp := Imported.True.

(* Isomorphism between Rocq True (in Prop) and Imported.True (in SProp) *)
(* Iso A B has: to : A -> B, from : B -> A, to_from : forall x:B, to (from x) = x, from_to : forall x:A, from (to x) = x *)
Instance True_iso : (Iso True imported_True).
Proof.
  unshelve econstructor.
  - (* to: True -> imported_True *)
    intro t. exact Imported.True_intro.
  - (* from: imported_True -> True *)
    intro impTrue. exact I.
  - (* to_from: forall x : imported_True, to (from x) = x -- equality in SProp *)
    (* Need to prove True_intro = x for x : imported_True in SProp *)
    (* SProp is proof irrelevant, so any two proofs are equal *)
    intro x. apply IsomorphismDefinitions.eq_refl.
  - (* from_to: forall x : True, from (to x) = x -- equality in Prop *)
    (* Need to prove I = x for x : True (Rocq's True in Prop) *)
    intro x. destruct x. apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant True := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.True := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor True True_iso := {}.
Instance: IsoStatementProofBetween True Imported.True True_iso := {}.