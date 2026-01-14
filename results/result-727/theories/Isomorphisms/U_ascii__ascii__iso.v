From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_Ascii_ascii : Type := Imported.Ascii_ascii.

(* Helper to convert bool to mybool *)
Definition bool_to_mybool (b : bool) : Imported.mybool :=
  match b with
  | true => Imported.mybool_mytrue
  | false => Imported.mybool_myfalse
  end.

Definition mybool_to_bool (b : Imported.mybool) : bool :=
  match b with
  | Imported.mybool_mytrue => true
  | Imported.mybool_myfalse => false
  end.

Definition ascii_to (a : Ascii.ascii) : imported_Ascii_ascii :=
  match a with
  | Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    Imported.Ascii_ascii_Ascii
      (bool_to_mybool b0) (bool_to_mybool b1) (bool_to_mybool b2) (bool_to_mybool b3)
      (bool_to_mybool b4) (bool_to_mybool b5) (bool_to_mybool b6) (bool_to_mybool b7)
  end.

Definition ascii_from (a : imported_Ascii_ascii) : Ascii.ascii :=
  match a with
  | Imported.Ascii_ascii_Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    Ascii.Ascii
      (mybool_to_bool b0) (mybool_to_bool b1) (mybool_to_bool b2) (mybool_to_bool b3)
      (mybool_to_bool b4) (mybool_to_bool b5) (mybool_to_bool b6) (mybool_to_bool b7)
  end.

Lemma ascii_to_from : forall x, IsomorphismDefinitions.eq (ascii_to (ascii_from x)) x.
Proof.
  intros [b0 b1 b2 b3 b4 b5 b6 b7].
  destruct b0, b1, b2, b3, b4, b5, b6, b7; apply IsomorphismDefinitions.eq_refl.
Defined.

Lemma ascii_from_to : forall x, IsomorphismDefinitions.eq (ascii_from (ascii_to x)) x.
Proof.
  intros [b0 b1 b2 b3 b4 b5 b6 b7].
  destruct b0, b1, b2, b3, b4, b5, b6, b7; apply IsomorphismDefinitions.eq_refl.
Defined.

Instance Ascii_ascii_iso : Iso Ascii.ascii imported_Ascii_ascii :=
  Build_Iso ascii_to ascii_from ascii_to_from ascii_from_to.
  
Instance: KnownConstant Ascii.ascii := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Ascii_ascii := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Ascii.ascii Ascii_ascii_iso := {}.
Instance: IsoStatementProofBetween Ascii.ascii Imported.Ascii_ascii Ascii_ascii_iso := {}.