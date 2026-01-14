From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_bool : Type := Imported.bool.

(* Build the isomorphism between bool and Imported.Coqbool *)
Definition bool_to_coqbool (b : bool) : Imported.Coqbool :=
  match b with
  | true => Imported.Coqbool_coqtrue
  | false => Imported.Coqbool_coqfalse
  end.

Definition coqbool_to_bool (b : Imported.Coqbool) : bool :=
  match b with
  | Imported.Coqbool_coqtrue => true
  | Imported.Coqbool_coqfalse => false
  end.

Instance bool_iso : Iso bool imported_bool :=
  {| to := bool_to_coqbool;
     from := coqbool_to_bool;
     to_from := fun b => match b with
       | Imported.Coqbool_coqtrue => IsomorphismDefinitions.eq_refl
       | Imported.Coqbool_coqfalse => IsomorphismDefinitions.eq_refl
       end;
     from_to := fun b => match b with
       | true => IsomorphismDefinitions.eq_refl
       | false => IsomorphismDefinitions.eq_refl
       end
  |}.

Instance: KnownConstant bool := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Coqbool := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor bool bool_iso := {}.
Instance: IsoStatementProofBetween bool Imported.Coqbool bool_iso := {}.