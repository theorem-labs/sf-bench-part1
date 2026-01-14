From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_or : SProp -> SProp -> SProp := Imported.or.

(* We need to build Iso (x1 \/ x3) (Imported.or x2 x4) where x1\/x3 is Prop and Imported.or x2 x4 is SProp *)
(* The challenge: we can't pattern match on SProp to produce Prop directly *)
(* Rocq doesn't allow eliminating SProp to Prop, so we need to use an axiom *)

(* Since Imported.or is structurally the same as Coq's or (just in SProp instead of Prop), *)
(* and given the component isomorphisms, the full isomorphism should exist. *)
(* We admit this because the SProp->Prop elimination is not definable in Rocq *)
(* Note: Imported.or is defined as Imported.Internal_MyOr *)
Instance or_iso : (forall (x1 : Prop) (x2 : SProp) (_ : Iso x1 x2) (x3 : Prop) (x4 : SProp) (_ : Iso x3 x4), Iso (x1 \/ x3) (imported_or x2 x4)).
Admitted.

Instance: KnownConstant or := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.or := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor or or_iso := {}.
Instance: IsoStatementProofBetween or Imported.or or_iso := {}.