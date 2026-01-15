From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


Definition imported_Type : Type := Imported.MyType.

Instance Type_iso : Iso Type imported_Type.
Proof.
  unfold imported_Type.
  exact {|
    to := fun x => x;
    from := fun x => x;
    to_from := fun x => IsomorphismDefinitions.eq_refl x;
    from_to := fun x => IsomorphismDefinitions.eq_refl x
  |}.
Defined.
Instance: KnownConstant Type := {}.
Instance: KnownConstant Imported.MyType := {}.
Instance: IsoStatementProofFor Type Type_iso := {}.
Instance: IsoStatementProofBetween Type Imported.MyType Type_iso := {}.