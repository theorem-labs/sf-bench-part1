From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_String_string : Type := Imported.String_string.

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

Fixpoint string_to_imported (s : String.string) : Imported.String_string :=
  match s with
  | String.EmptyString => Imported.String_string_EmptyString
  | String.String a s' => Imported.String_string_String (ascii_to_imported a) (string_to_imported s')
  end.

Fixpoint imported_to_string (s : Imported.String_string) : String.string :=
  match s with
  | Imported.String_string_EmptyString => String.EmptyString
  | Imported.String_string_String a s' => String.String (imported_to_ascii a) (imported_to_string s')
  end.

Definition bool_mybool_roundtrip1 (b : bool) : @Logic.eq _ (mybool_to_bool (bool_to_mybool b)) b :=
  match b with true => Logic.eq_refl | false => Logic.eq_refl end.

Definition bool_mybool_roundtrip2 (b : Imported.mybool) : @Logic.eq _ (bool_to_mybool (mybool_to_bool b)) b :=
  match b with Imported.mybool_mytrue => Logic.eq_refl | Imported.mybool_myfalse => Logic.eq_refl end.

Definition ascii_roundtrip1 (a : Ascii.ascii) : @Logic.eq _ (imported_to_ascii (ascii_to_imported a)) a.
Proof.
  destruct a as [b0 b1 b2 b3 b4 b5 b6 b7].
  unfold ascii_to_imported, imported_to_ascii.
  destruct b0, b1, b2, b3, b4, b5, b6, b7; exact Logic.eq_refl.
Defined.

Definition ascii_roundtrip2 (a : Imported.Ascii_ascii) : @Logic.eq _ (ascii_to_imported (imported_to_ascii a)) a.
Proof.
  destruct a as [b0 b1 b2 b3 b4 b5 b6 b7].
  unfold imported_to_ascii, ascii_to_imported.
  destruct b0, b1, b2, b3, b4, b5, b6, b7; exact Logic.eq_refl.
Defined.

Fixpoint string_roundtrip1 (s : Imported.String_string) : @Logic.eq _ (string_to_imported (imported_to_string s)) s :=
  match s with
  | Imported.String_string_EmptyString => Logic.eq_refl
  | Imported.String_string_String a s' =>
    Logic.f_equal2 Imported.String_string_String (ascii_roundtrip2 a) (string_roundtrip1 s')
  end.

Fixpoint string_roundtrip2 (s : String.string) : @Logic.eq _ (imported_to_string (string_to_imported s)) s :=
  match s with
  | String.EmptyString => Logic.eq_refl
  | String.String a s' =>
    Logic.f_equal2 String.String (ascii_roundtrip1 a) (string_roundtrip2 s')
  end.

Instance String_string_iso : Iso String.string imported_String_string.
Proof.
  exact (Build_Iso string_to_imported imported_to_string
    (fun s => seq_of_eq (string_roundtrip1 s))
    (fun s => seq_of_eq (string_roundtrip2 s))).
Defined.
Instance: KnownConstant String.string := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.String_string := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor String.string String_string_iso := {}.
Instance: IsoStatementProofBetween String.string Imported.String_string String_string_iso := {}.