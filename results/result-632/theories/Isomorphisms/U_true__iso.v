From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

Definition imported_True : SProp := Imported.True.

Instance True_iso : (Iso True imported_True).
Proof.
  refine {|
    to := fun _ => Imported.True_intro;
    from := fun _ => Logic.I;
    to_from := _;
    from_to := _
  |}.
  (* to_from: show Imported.True_intro = t for t : Imported.True (SProp) *)
  (* SProp is proof irrelevant, so eq_refl works *)
  intro t. exact IsomorphismDefinitions.eq_refl.
  (* from_to: show I = t for t : True (Prop) *)
  intro t. destruct t. exact IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant True := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.True := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor True True_iso := {}.
Instance: IsoStatementProofBetween True Imported.True True_iso := {}.