From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


(* Imported.True is in SProp, Coq True is in Prop. We use iso_Prop_SProp. *)
Definition imported_True : SProp := Imported.True.

(* True is a unit type (one element), so isomorphism is straightforward *)
Definition true_to_imported (t : True) : Imported.True := Imported.True_intro.
Definition imported_to_true (t : Imported.True) : True := I.

(* For from_to, we need eq (imported_to_true (true_to_imported t)) t *)
(* which is eq I t, and since True has only I, this holds *)
Definition from_to_true (t : True) : IsomorphismDefinitions.eq (imported_to_true (true_to_imported t)) t :=
  match t with
  | I => IsomorphismDefinitions.eq_refl
  end.

Instance True_iso : (Iso True imported_True) := {|
  to := true_to_imported;
  from := imported_to_true;
  to_from := fun _ => IsomorphismDefinitions.eq_refl;
  from_to := from_to_true
|}.

Instance: KnownConstant True := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.True := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor True True_iso := {}.
Instance: IsoStatementProofBetween True Imported.True True_iso := {}.