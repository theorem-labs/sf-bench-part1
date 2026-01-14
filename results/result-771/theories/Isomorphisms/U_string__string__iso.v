From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
From IsomorphismChecker Require Export Isomorphisms.bool__iso.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

(* We need to build an isomorphism between String.string and Imported.String_string *)
(* String.string is: EmptyString | String ascii string *)
(* Imported.Coqstring is: Coqstring_EmptyString | Coqstring_String Coqascii Coqstring *)
(* Imported.Coqascii has 8 Coqbool fields matching Ascii.ascii's 8 bool constructor args *)

(* Convert between Ascii.ascii and Imported.Coqascii *)
Definition ascii_to_imported (a : Ascii.ascii) : Imported.Coqascii :=
  match a with
  | Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    Imported.Coqascii_Ascii (bool_to_coqbool b0) (bool_to_coqbool b1) (bool_to_coqbool b2) (bool_to_coqbool b3)
                            (bool_to_coqbool b4) (bool_to_coqbool b5) (bool_to_coqbool b6) (bool_to_coqbool b7)
  end.

Definition imported_to_ascii (a : Imported.Coqascii) : Ascii.ascii :=
  Ascii.Ascii 
    (coqbool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_maps__U2_lf__U_maps__update____example3__iso__hyg26 a))
    (coqbool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_maps__U2_lf__U_maps__update____example3__iso__hyg28 a))
    (coqbool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_maps__U2_lf__U_maps__update____example3__iso__hyg30 a))
    (coqbool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_maps__U2_lf__U_maps__update____example3__iso__hyg32 a))
    (coqbool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_maps__U2_lf__U_maps__update____example3__iso__hyg34 a))
    (coqbool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_maps__U2_lf__U_maps__update____example3__iso__hyg36 a))
    (coqbool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_maps__U2_lf__U_maps__update____example3__iso__hyg38 a))
    (coqbool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_maps__U2_lf__U_maps__update____example3__iso__hyg40 a)).

(* Convert between String.string and Imported.Coqstring *)
Fixpoint string_to_imported (s : String.string) : Imported.Coqstring :=
  match s with
  | String.EmptyString => Imported.Coqstring_EmptyString
  | String.String c rest => Imported.Coqstring_String (ascii_to_imported c) (string_to_imported rest)
  end.

Fixpoint imported_to_string (s : Imported.Coqstring) : String.string :=
  match s with
  | Imported.Coqstring_EmptyString => String.EmptyString
  | Imported.Coqstring_String c rest => String.String (imported_to_ascii c) (imported_to_string rest)
  end.

(* Roundtrip lemmas *)
Lemma ascii_roundtrip : forall a, IsomorphismDefinitions.eq (imported_to_ascii (ascii_to_imported a)) a.
Proof.
  intros [b0 b1 b2 b3 b4 b5 b6 b7].
  unfold ascii_to_imported, imported_to_ascii. simpl.
  destruct b0, b1, b2, b3, b4, b5, b6, b7; exact IsomorphismDefinitions.eq_refl.
Qed.

Lemma bool_coqbool_roundtrip2 : forall b, bool_to_coqbool (coqbool_to_bool b) = b.
Proof. destruct b; reflexivity. Qed.

Lemma imported_ascii_roundtrip : forall a, IsomorphismDefinitions.eq (ascii_to_imported (imported_to_ascii a)) a.
Proof.
  intros a. destruct a.
  unfold imported_to_ascii, ascii_to_imported. simpl.
  repeat rewrite bool_coqbool_roundtrip2.
  apply IsomorphismDefinitions.eq_refl.
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
    destruct c.
    simpl. repeat rewrite bool_coqbool_roundtrip2.
    exact (IsoEq.f_equal (fun r => Imported.Coqstring_String _ r) (IH rest)).
Qed.

Definition imported_String_string : Type := Imported.Coqstring.

Instance String_string_iso : Iso String.string imported_String_string :=
  Build_Iso string_to_imported imported_to_string imported_string_roundtrip string_roundtrip.

Instance: KnownConstant String.string := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Coqstring := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor String.string String_string_iso := {}.
Instance: IsoStatementProofBetween String.string Imported.Coqstring String_string_iso := {}.