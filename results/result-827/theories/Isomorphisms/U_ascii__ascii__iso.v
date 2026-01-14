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

(* Use the same conversion functions as bool__iso *)
Definition bool_to_mybool := bool_to_imported.
Definition mybool_to_bool := imported_to_bool.

Definition ascii_to_imported (a : Ascii.ascii) : Imported.Ascii_ascii :=
  match a with
  | Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    Imported.Ascii_ascii_Ascii
      (bool_to_mybool b0) (bool_to_mybool b1) (bool_to_mybool b2) (bool_to_mybool b3)
      (bool_to_mybool b4) (bool_to_mybool b5) (bool_to_mybool b6) (bool_to_mybool b7)
  end.

Definition imported_to_ascii (a : Imported.Ascii_ascii) : Ascii.ascii :=
  match a with
  | Imported.Ascii_ascii_Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    Ascii.Ascii (mybool_to_bool b0) (mybool_to_bool b1) (mybool_to_bool b2) (mybool_to_bool b3)
                (mybool_to_bool b4) (mybool_to_bool b5) (mybool_to_bool b6) (mybool_to_bool b7)
  end.

Definition ascii_roundtrip1 (a : Imported.Ascii_ascii) : @Logic.eq _ (ascii_to_imported (imported_to_ascii a)) a.
Proof.
  destruct a as [b0 b1 b2 b3 b4 b5 b6 b7].
  unfold imported_to_ascii, ascii_to_imported.
  destruct b0, b1, b2, b3, b4, b5, b6, b7; exact Logic.eq_refl.
Defined.

Definition ascii_roundtrip2 (a : Ascii.ascii) : @Logic.eq _ (imported_to_ascii (ascii_to_imported a)) a.
Proof.
  destruct a as [b0 b1 b2 b3 b4 b5 b6 b7].
  unfold ascii_to_imported, imported_to_ascii.
  destruct b0, b1, b2, b3, b4, b5, b6, b7; exact Logic.eq_refl.
Defined.

Instance Ascii_ascii_iso : Iso Ascii.ascii imported_Ascii_ascii.
Proof.
  exact (Build_Iso ascii_to_imported imported_to_ascii
    (fun a => seq_of_eq (ascii_roundtrip1 a))
    (fun a => seq_of_eq (ascii_roundtrip2 a))).
Defined.
Instance: KnownConstant Ascii.ascii := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Ascii_ascii := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Ascii.ascii Ascii_ascii_iso := {}.
Instance: IsoStatementProofBetween Ascii.ascii Imported.Ascii_ascii Ascii_ascii_iso := {}.