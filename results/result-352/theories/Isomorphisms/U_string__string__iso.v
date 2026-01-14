From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_String_string : Type := Imported.String_string.

(* First: bool <-> Imported.Bool *)
Definition bool_to_Bool (b : bool) : Imported.Bool :=
  match b with
  | true => Imported.Bool_true
  | false => Imported.Bool_false
  end.

Definition Bool_to_bool (b : Imported.Bool) : bool :=
  match b with
  | Imported.Bool_true => true
  | Imported.Bool_false => false
  end.

Lemma bool_Bool_to_from : forall b, bool_to_Bool (Bool_to_bool b) = b.
Proof.
  intro b. destruct b; reflexivity.
Qed.

Lemma bool_Bool_from_to : forall b, Bool_to_bool (bool_to_Bool b) = b.
Proof.
  intro b. destruct b; reflexivity.
Qed.

(* Second: Ascii.ascii <-> Imported.ascii *)
Definition ascii_to_imported (a : Ascii.ascii) : Imported.ascii :=
  match a with
  | Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
      Imported.ascii_Ascii (bool_to_Bool b0) (bool_to_Bool b1) (bool_to_Bool b2) (bool_to_Bool b3)
                           (bool_to_Bool b4) (bool_to_Bool b5) (bool_to_Bool b6) (bool_to_Bool b7)
  end.

Definition imported_to_ascii (a : Imported.ascii) : Ascii.ascii :=
  match a with
  | Imported.ascii_Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
      Ascii.Ascii (Bool_to_bool b0) (Bool_to_bool b1) (Bool_to_bool b2) (Bool_to_bool b3)
                  (Bool_to_bool b4) (Bool_to_bool b5) (Bool_to_bool b6) (Bool_to_bool b7)
  end.

(* Third: String.string <-> Imported.String_string *)
Fixpoint string_to_imported (s : String.string) : Imported.String_string :=
  match s with
  | String.EmptyString => Imported.String_string_EmptyString
  | String.String a rest => Imported.String_string_String (ascii_to_imported a) (string_to_imported rest)
  end.

Fixpoint imported_to_string (s : Imported.String_string) : String.string :=
  match s with
  | Imported.String_string_EmptyString => String.EmptyString
  | Imported.String_string_String a rest => String.String (imported_to_ascii a) (imported_to_string rest)
  end.

(* Proofs using IsomorphismDefinitions.eq *)
Lemma bool_to_from_iso : forall b : Imported.Bool, IsomorphismDefinitions.eq (bool_to_Bool (Bool_to_bool b)) b.
Proof.
  intro b. destruct b; apply IsomorphismDefinitions.eq_refl.
Qed.

Lemma bool_from_to_iso : forall b : bool, IsomorphismDefinitions.eq (Bool_to_bool (bool_to_Bool b)) b.
Proof.
  intro b. destruct b; apply IsomorphismDefinitions.eq_refl.
Qed.

Lemma ascii_to_from_iso : forall a : Imported.ascii, IsomorphismDefinitions.eq (ascii_to_imported (imported_to_ascii a)) a.
Proof.
  intro a.
  unfold imported_to_ascii, ascii_to_imported.
  destruct a as [b0 b1 b2 b3 b4 b5 b6 b7]. simpl.
  (* For primitive records with eta, we need to show each field is equal *)
  destruct b0; destruct b1; destruct b2; destruct b3; 
  destruct b4; destruct b5; destruct b6; destruct b7;
  apply IsomorphismDefinitions.eq_refl.
Qed.

Lemma ascii_from_to_iso : forall a : Ascii.ascii, IsomorphismDefinitions.eq (imported_to_ascii (ascii_to_imported a)) a.
Proof.
  intro a. destruct a as [b0 b1 b2 b3 b4 b5 b6 b7].
  unfold imported_to_ascii, ascii_to_imported. simpl.
  destruct b0; destruct b1; destruct b2; destruct b3;
  destruct b4; destruct b5; destruct b6; destruct b7;
  apply IsomorphismDefinitions.eq_refl.
Qed.

Fixpoint string_to_from_iso (s : Imported.String_string) : IsomorphismDefinitions.eq (string_to_imported (imported_to_string s)) s :=
  match s with
  | Imported.String_string_EmptyString => IsomorphismDefinitions.eq_refl
  | Imported.String_string_String a rest =>
      IsoEq.f_equal2 Imported.String_string_String (ascii_to_from_iso a) (string_to_from_iso rest)
  end.

Fixpoint string_from_to_iso (s : String.string) : IsomorphismDefinitions.eq (imported_to_string (string_to_imported s)) s :=
  match s with
  | String.EmptyString => IsomorphismDefinitions.eq_refl
  | String.String a rest =>
      IsoEq.f_equal2 String.String (ascii_from_to_iso a) (string_from_to_iso rest)
  end.

Instance String_string_iso : Iso String.string imported_String_string.
Proof.
  unshelve eapply Build_Iso.
  - exact string_to_imported.
  - exact imported_to_string.
  - exact string_to_from_iso.
  - exact string_from_to_iso.
Defined.

Instance: KnownConstant String.string := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.String_string := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor String.string String_string_iso := {}.
Instance: IsoStatementProofBetween String.string Imported.String_string String_string_iso := {}.
