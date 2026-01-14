From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

(* Imported.True : SProp, Logic.True : Prop *)
Definition imported_True := Imported.True.

(* We need Iso Logic.True Imported.True *)
(* Build_Iso needs: to from to_from from_to *)
(* to : Logic.True -> imported_True *)
(* from : imported_True -> Logic.True *)
(* to_from : forall x, to (from x) = x  (in SProp) *)
(* from_to : forall x, from (to x) = x  (in SProp) *)
Instance True_iso : (Iso Logic.True imported_True).
Proof.
  refine {|
    to := fun _ => Imported.True_intro;
    from := fun _ => Logic.I;
    to_from := _;
    from_to := _
  |}.
  - intro x. exact (IsomorphismDefinitions.eq_refl _).
  - intro x. destruct x. exact (IsomorphismDefinitions.eq_refl _).
Defined.
Instance: KnownConstant Logic.True := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.True := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Logic.True True_iso := {}.
Instance: IsoStatementProofBetween Logic.True Imported.True True_iso := {}.