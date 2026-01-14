From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

(* We need to build an isomorphism between String.string and Imported.String_string *)
(* String.string is: EmptyString | String ascii string *)
(* Imported.String_string is: EmptyString | String ascii String_string *)
(* Imported.ascii has 8 Bool fields matching Ascii.ascii's 8 bool constructor args *)

(* First, convert between Coq bool and Imported.Bool *)
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

(* Convert between Ascii.ascii and Imported.ascii *)
Definition ascii_to_imported (a : Ascii.ascii) : Imported.ascii :=
  match a with
  | Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    Imported.ascii_Ascii (bool_to_Bool b0) (bool_to_Bool b1) (bool_to_Bool b2) (bool_to_Bool b3)
                         (bool_to_Bool b4) (bool_to_Bool b5) (bool_to_Bool b6) (bool_to_Bool b7)
  end.

Definition imported_to_ascii (a : Imported.ascii) : Ascii.ascii :=
  Ascii.Ascii 
    (Bool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_maps__U2_lf__U_maps__update____same__iso__hyg36 a))
    (Bool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_maps__U2_lf__U_maps__update____same__iso__hyg38 a))
    (Bool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_maps__U2_lf__U_maps__update____same__iso__hyg40 a))
    (Bool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_maps__U2_lf__U_maps__update____same__iso__hyg42 a))
    (Bool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_maps__U2_lf__U_maps__update____same__iso__hyg44 a))
    (Bool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_maps__U2_lf__U_maps__update____same__iso__hyg46 a))
    (Bool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_maps__U2_lf__U_maps__update____same__iso__hyg48 a))
    (Bool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_maps__U2_lf__U_maps__update____same__iso__hyg50 a)).

(* Convert between String.string and Imported.String_string *)
Fixpoint string_to_imported (s : String.string) : Imported.String_string :=
  match s with
  | String.EmptyString => Imported.String_string_EmptyString
  | String.String c rest => Imported.String_string_String (ascii_to_imported c) (string_to_imported rest)
  end.

Fixpoint imported_to_string (s : Imported.String_string) : String.string :=
  match s with
  | Imported.String_string_EmptyString => String.EmptyString
  | Imported.String_string_String c rest => String.String (imported_to_ascii c) (imported_to_string rest)
  end.

(* Roundtrip lemmas - using IsomorphismDefinitions.eq which is in SProp *)
(* Note: `=` here is IsomorphismDefinitions.eq due to the imports above *)
Lemma bool_Bool_roundtrip : forall b, IsomorphismDefinitions.eq (Bool_to_bool (bool_to_Bool b)) b.
Proof. destruct b; exact IsomorphismDefinitions.eq_refl. Qed.

Lemma Bool_bool_roundtrip : forall b, IsomorphismDefinitions.eq (bool_to_Bool (Bool_to_bool b)) b.
Proof. destruct b; exact IsomorphismDefinitions.eq_refl. Qed.

Lemma ascii_roundtrip : forall a, IsomorphismDefinitions.eq (imported_to_ascii (ascii_to_imported a)) a.
Proof.
  intros [b0 b1 b2 b3 b4 b5 b6 b7].
  unfold ascii_to_imported, imported_to_ascii. simpl.
  destruct b0, b1, b2, b3, b4, b5, b6, b7; exact IsomorphismDefinitions.eq_refl.
Qed.

Lemma imported_ascii_roundtrip : forall a, IsomorphismDefinitions.eq (ascii_to_imported (imported_to_ascii a)) a.
Proof.
  intros a. destruct a as [b0 b1 b2 b3 b4 b5 b6 b7].
  unfold imported_to_ascii, ascii_to_imported. simpl.
  destruct b0, b1, b2, b3, b4, b5, b6, b7; exact IsomorphismDefinitions.eq_refl.
Qed.

Lemma string_roundtrip : forall s, IsomorphismDefinitions.eq (imported_to_string (string_to_imported s)) s.
Proof.
  fix IH 1.
  intros s. destruct s as [|c rest].
  - simpl. exact IsomorphismDefinitions.eq_refl.
  - simpl.
    destruct c as [b0 b1 b2 b3 b4 b5 b6 b7].
    destruct b0, b1, b2, b3, b4, b5, b6, b7; simpl;
    exact (IsoEq.f_equal (fun r => String.String _ r) (IH rest)).
Qed.

Lemma imported_string_roundtrip : forall s, IsomorphismDefinitions.eq (string_to_imported (imported_to_string s)) s.
Proof.
  fix IH 1.
  intros s. destruct s as [|c rest].
  - simpl. exact IsomorphismDefinitions.eq_refl.
  - simpl.
    destruct c as [b0 b1 b2 b3 b4 b5 b6 b7].
    destruct b0, b1, b2, b3, b4, b5, b6, b7; simpl;
    exact (IsoEq.f_equal (fun r => Imported.String_string_String _ r) (IH rest)).
Qed.

Definition imported_String_string : Type := Imported.String_string.

Instance String_string_iso : Iso String.string imported_String_string :=
  Build_Iso string_to_imported imported_to_string imported_string_roundtrip string_roundtrip.

Instance: KnownConstant String.string := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.String_string := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor String.string String_string_iso := {}.
Instance: IsoStatementProofBetween String.string Imported.String_string String_string_iso := {}.