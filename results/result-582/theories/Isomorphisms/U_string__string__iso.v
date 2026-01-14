From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso. (* for speed *)
Require Import Stdlib.Strings.String.
Require Import Stdlib.Strings.Ascii.

(* Need bool isomorphism for ascii *)
Definition to_bool (b : Datatypes.bool) : Imported.mybool :=
  match b with
  | Datatypes.true => Imported.mybool_mytrue
  | Datatypes.false => Imported.mybool_myfalse
  end.

Definition from_bool (b : Imported.mybool) : Datatypes.bool :=
  match b with
  | Imported.mybool_mytrue => Datatypes.true
  | Imported.mybool_myfalse => Datatypes.false
  end.

Lemma to_from_bool : forall b, eq (to_bool (from_bool b)) b.
Proof. intros []; simpl; apply eq_refl. Qed.

Lemma from_to_bool : forall b, eq (from_bool (to_bool b)) b.
Proof. intros []; apply eq_refl. Qed.

(* Need ascii isomorphism *)
Definition to_ascii (a : Ascii.ascii) : Imported.Ascii_ascii :=
  match a with
  | Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
      Imported.Ascii_ascii_Ascii (to_bool b0) (to_bool b1) (to_bool b2) (to_bool b3)
                     (to_bool b4) (to_bool b5) (to_bool b6) (to_bool b7)
  end.

Definition from_ascii (a : Imported.Ascii_ascii) : Ascii.ascii :=
  match a with
  | Imported.Ascii_ascii_Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
      Ascii.Ascii (from_bool b0) (from_bool b1) (from_bool b2) (from_bool b3)
                  (from_bool b4) (from_bool b5) (from_bool b6) (from_bool b7)
  end.

Lemma to_from_ascii : forall a, eq (to_ascii (from_ascii a)) a.
Proof.
  intros [b0 b1 b2 b3 b4 b5 b6 b7].
  unfold to_ascii, from_ascii; simpl.
  destruct b0, b1, b2, b3, b4, b5, b6, b7; simpl; apply eq_refl.
Qed.

Lemma from_to_ascii : forall a, eq (from_ascii (to_ascii a)) a.
Proof.
  intros [b0 b1 b2 b3 b4 b5 b6 b7].
  unfold to_ascii, from_ascii; simpl.
  destruct b0, b1, b2, b3, b4, b5, b6, b7; simpl; apply eq_refl.
Qed.

Definition imported_String_string : Type := Imported.String_string.

(* String isomorphism *)
Fixpoint string_to_String_string (s : string) : Imported.String_string :=
  match s with
  | EmptyString => Imported.String_string_EmptyString
  | String c s' => Imported.String_string_String (to_ascii c) (string_to_String_string s')
  end.

Fixpoint String_string_to_string (s : Imported.String_string) : string :=
  match s with
  | Imported.String_string_EmptyString => EmptyString
  | Imported.String_string_String c s' => String (from_ascii c) (String_string_to_string s')
  end.

Lemma string_to_from : forall s, eq (string_to_String_string (String_string_to_string s)) s.
Proof.
  fix to_from 1.
  intros s.
  destruct s; simpl.
  - apply eq_refl.
  - apply (IsoEq.f_equal2 Imported.String_string_String).
    + apply to_from_ascii.
    + apply to_from.
Qed.

Lemma string_from_to : forall s, eq (String_string_to_string (string_to_String_string s)) s.
Proof.
  fix from_to 1.
  intros s.
  destruct s; simpl.
  - apply eq_refl.
  - apply (IsoEq.f_equal2 String).
    + apply from_to_ascii.
    + apply from_to.
Qed.

Instance String_string_iso : Iso String.string imported_String_string :=
  Build_Iso string_to_String_string String_string_to_string string_to_from string_from_to.

Instance: KnownConstant String.string := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.String_string := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor String.string String_string_iso := {}.
Instance: IsoStatementProofBetween String.string Imported.String_string String_string_iso := {}.
