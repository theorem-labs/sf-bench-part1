From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_false__iso.

(* Logic.not is defined as (P -> False), so imported_Logic_not is (x2 -> imported_False) *)
Definition imported_Logic_not : SProp -> SProp := fun x2 : SProp => x2 -> imported_False.
Instance Logic_not_iso : forall (x1 : Prop) (x2 : SProp), Iso x1 x2 -> Iso (~ x1) (imported_Logic_not x2)
  := fun (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) => IsoArrow hx False_iso.

Instance: KnownConstant Logic.not := {}. (* only needed when rel_iso is typeclasses opaque *)
(* Note: There is no Imported.Logic_not, we define it here *)
Instance: IsoStatementProofFor Logic.not Logic_not_iso := {}.