From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_false__iso.

(* Imported.Logic_not P = P -> Imported.False *)
(* So imported_Logic_not = Imported.Logic_not *)
Definition imported_Logic_not : SProp -> SProp := Imported.Logic_not.

(* Prove that ~ x1 is isomorphic to imported_Logic_not x2 when x1 ~ x2 *)
Instance Logic_not_iso : forall (x1 : Prop) (x2 : SProp), Iso x1 x2 -> Iso (~ x1) (imported_Logic_not x2).
Proof.
  intros x1 x2 hx.
  unfold imported_Logic_not, Imported.Logic_not.
  (* ~ x1 = x1 -> False, imported_Logic_not x2 = x2 -> imported_False *)
  apply IsoArrow.
  - exact hx.
  - exact False_iso.
Defined.

Instance: KnownConstant Logic.not := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Logic_not := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Logic.not Logic_not_iso := {}.
Instance: IsoStatementProofBetween Logic.not Imported.Logic_not Logic_not_iso := {}.