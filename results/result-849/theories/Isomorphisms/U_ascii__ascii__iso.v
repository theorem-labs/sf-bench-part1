From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.bool__iso.

Definition imported_Ascii_ascii : Type := Imported.Ascii_ascii.

Instance Ascii_ascii_iso : Iso Ascii.ascii imported_Ascii_ascii.
Proof.
  unshelve eapply Build_Iso.
  - (* to : Ascii.ascii -> Imported.Ascii_ascii *)
    intro a. destruct a as [b0 b1 b2 b3 b4 b5 b6 b7].
    exact (Imported.Ascii_ascii_Ascii_Ascii
      (to bool_iso b0) (to bool_iso b1) (to bool_iso b2) (to bool_iso b3)
      (to bool_iso b4) (to bool_iso b5) (to bool_iso b6) (to bool_iso b7)).
  - (* from : Imported.Ascii_ascii -> Ascii.ascii *)
    intro a. destruct a as [b0 b1 b2 b3 b4 b5 b6 b7].
    exact (Ascii.Ascii
      (from bool_iso b0) (from bool_iso b1) (from bool_iso b2) (from bool_iso b3)
      (from bool_iso b4) (from bool_iso b5) (from bool_iso b6) (from bool_iso b7)).
  - (* to_from *)
    intro a. destruct a as [b0 b1 b2 b3 b4 b5 b6 b7].
    destruct b0; destruct b1; destruct b2; destruct b3;
    destruct b4; destruct b5; destruct b6; destruct b7;
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro a. destruct a as [b0 b1 b2 b3 b4 b5 b6 b7].
    destruct b0; destruct b1; destruct b2; destruct b3;
    destruct b4; destruct b5; destruct b6; destruct b7;
    apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Ascii.ascii := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Ascii_ascii := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Ascii.ascii Ascii_ascii_iso := {}.
Instance: IsoStatementProofBetween Ascii.ascii Imported.Ascii_ascii Ascii_ascii_iso := {}.