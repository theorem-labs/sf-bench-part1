From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

(* The exported type is Imported.bool *)
Definition imported_bool : Type := Imported.bool.

(* Define the isomorphism between bool and Imported.bool *)
Definition bool_to_imported (b : bool) : Imported.bool :=
  match b with
  | true => Imported.bool_true
  | false => Imported.bool_false
  end.

Definition imported_to_bool (b : Imported.bool) : bool :=
  match b with
  | Imported.bool_true => true
  | Imported.bool_false => false
  end.

Instance bool_iso : Iso bool imported_bool :=
  {|
    to := bool_to_imported;
    from := imported_to_bool;
    to_from := fun b => match b with
                        | Imported.bool_true => IsomorphismDefinitions.eq_refl
                        | Imported.bool_false => IsomorphismDefinitions.eq_refl
                        end;
    from_to := fun b => match b with
                        | true => IsomorphismDefinitions.eq_refl
                        | false => IsomorphismDefinitions.eq_refl
                        end
  |}.

Instance: KnownConstant bool := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.bool := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor bool bool_iso := {}.
Instance: IsoStatementProofBetween bool Imported.bool bool_iso := {}.
