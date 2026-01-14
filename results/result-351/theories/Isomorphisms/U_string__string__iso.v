From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Strings.Ascii.
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_String_string : Type := Imported.String_string.

(* Convert between bool and Imported.Bool *)
Definition bool_to_imported (b : bool) : Imported.Bool :=
  match b with
  | true => Imported.Bool_true
  | false => Imported.Bool_false
  end.

Definition bool_from_imported (b : Imported.Bool) : bool :=
  match b with
  | Imported.Bool_true => true
  | Imported.Bool_false => false
  end.

(* Convert ascii characters *)
Definition ascii_to_imported (a : Ascii.ascii) : Imported.ascii :=
  match a with
  | Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    Imported.ascii_Ascii 
      (bool_to_imported b0) (bool_to_imported b1) 
      (bool_to_imported b2) (bool_to_imported b3)
      (bool_to_imported b4) (bool_to_imported b5) 
      (bool_to_imported b6) (bool_to_imported b7)
  end.

Definition ascii_from_imported (a : Imported.ascii) : Ascii.ascii :=
  match a with
  | Imported.ascii_Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    Ascii.Ascii 
      (bool_from_imported b0) (bool_from_imported b1) 
      (bool_from_imported b2) (bool_from_imported b3)
      (bool_from_imported b4) (bool_from_imported b5) 
      (bool_from_imported b6) (bool_from_imported b7)
  end.

Lemma ascii_to_from : forall a, IsomorphismDefinitions.eq (ascii_to_imported (ascii_from_imported a)) a.
Proof.
  intro a. destruct a as [b0 b1 b2 b3 b4 b5 b6 b7].
  unfold ascii_from_imported, ascii_to_imported.
  destruct b0, b1, b2, b3, b4, b5, b6, b7; apply IsomorphismDefinitions.eq_refl.
Qed.

Lemma ascii_from_to : forall a, IsomorphismDefinitions.eq (ascii_from_imported (ascii_to_imported a)) a.
Proof.
  intro a. destruct a as [b0 b1 b2 b3 b4 b5 b6 b7].
  unfold ascii_to_imported, ascii_from_imported.
  destruct b0, b1, b2, b3, b4, b5, b6, b7; apply IsomorphismDefinitions.eq_refl.
Qed.

(* Convert strings *)
Fixpoint string_to_imported (s : String.string) : Imported.String_string :=
  match s with
  | EmptyString => Imported.String_string_EmptyString
  | String c s' => Imported.String_string_String (ascii_to_imported c) (string_to_imported s')
  end.

Fixpoint string_from_imported (s : Imported.String_string) : String.string :=
  match s with
  | Imported.String_string_EmptyString => EmptyString
  | Imported.String_string_String c s' => String (ascii_from_imported c) (string_from_imported s')
  end.

Lemma string_to_from : forall s, IsomorphismDefinitions.eq (string_to_imported (string_from_imported s)) s.
Proof.
  fix IH 1.
  intro s. destruct s.
  - apply IsomorphismDefinitions.eq_refl.
  - simpl. apply (f_equal2 Imported.String_string_String).
    + apply ascii_to_from.
    + apply IH.
Qed.

Lemma string_from_to : forall s, IsomorphismDefinitions.eq (string_from_imported (string_to_imported s)) s.
Proof.
  fix IH 1.
  intro s. destruct s.
  - apply IsomorphismDefinitions.eq_refl.
  - simpl. apply (f_equal2 String).
    + apply ascii_from_to.
    + apply IH.
Qed.

Instance String_string_iso : Iso String.string imported_String_string.
Proof.
  unshelve eapply Build_Iso.
  - exact string_to_imported.
  - exact string_from_imported.
  - exact string_to_from.
  - exact string_from_to.
Defined.
Instance: KnownConstant String.string := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.String_string := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor String.string String_string_iso := {}.
Instance: IsoStatementProofBetween String.string Imported.String_string String_string_iso := {}.
