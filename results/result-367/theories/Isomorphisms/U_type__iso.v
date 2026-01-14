From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_Type : Type := Imported.Type.

(* Both Type and Imported.Type are the same, so isomorphism is trivial *)
Instance Type_iso : Iso Type imported_Type.
Proof.
  unfold imported_Type.
  (* Imported.Type is definitionally equal to Type *)
  exact {|
    to := fun x => x;
    from := fun x => x;
    to_from := fun x => IsomorphismDefinitions.eq_refl x;
    from_to := fun x => IsomorphismDefinitions.eq_refl x
  |}.
Defined.
Instance: KnownConstant Type := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Type := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Type Type_iso := {}.
Instance: IsoStatementProofBetween Type Imported.Type Type_iso := {}.