From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

(* Imported.True is in SProp, and True in Rocq is in Prop *)
Definition imported_True : SProp := Imported.True.

(* True is a unit type, so any element equals I *)
Lemma true_unique : forall (x : True), x = I.
Proof.
  intro x. destruct x. reflexivity.
Qed.

Instance True_iso : (Iso True imported_True) :=
  Build_Iso (fun _ => Imported.True_intro) (fun _ => I)
    (fun _ => IsomorphismDefinitions.eq_refl)
    (fun x => eq_sym (seq_of_eq (true_unique x))).

Instance: KnownConstant True := {}.
Instance: KnownConstant Imported.True := {}.
Instance: IsoStatementProofFor True True_iso := {}.
Instance: IsoStatementProofBetween True Imported.True True_iso := {}.