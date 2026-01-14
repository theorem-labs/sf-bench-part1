From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

(* The exported type is Imported.bool (alias for mybool) *)
Definition imported_bool : Type := Imported.bool.

(* Define the isomorphism between bool and Imported.mybool *)
Definition bool_to_imported (b : bool) : Imported.mybool :=
  match b with
  | true => Imported.mybool_true
  | false => Imported.mybool_false
  end.

Definition imported_to_bool (b : Imported.mybool) : bool :=
  match b with
  | Imported.mybool_true => true
  | Imported.mybool_false => false
  end.

Instance bool_iso : Iso bool imported_bool :=
  {|
    to := bool_to_imported;
    from := imported_to_bool;
    to_from := fun b => match b with
                        | Imported.mybool_true => IsomorphismDefinitions.eq_refl
                        | Imported.mybool_false => IsomorphismDefinitions.eq_refl
                        end;
    from_to := fun b => match b with
                        | true => IsomorphismDefinitions.eq_refl
                        | false => IsomorphismDefinitions.eq_refl
                        end
  |}.

Instance: KnownConstant bool := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.mybool := {}.
Instance: KnownConstant Imported.bool := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor bool bool_iso := {}.
Instance: IsoStatementProofBetween bool Imported.mybool bool_iso := {}.
