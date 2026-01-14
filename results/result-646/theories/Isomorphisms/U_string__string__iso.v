From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.bool__iso.

Definition imported_String_string : Type := Imported.String_string.

(* ascii isomorphism *)
Definition ascii_to_imported (a : Ascii.ascii) : Imported.myascii :=
  match a with
  | Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
      Imported.myascii_Ascii (bool_to_imported b0) (bool_to_imported b1) 
                              (bool_to_imported b2) (bool_to_imported b3)
                              (bool_to_imported b4) (bool_to_imported b5) 
                              (bool_to_imported b6) (bool_to_imported b7)
  end.

Definition imported_to_ascii (a : Imported.myascii) : Ascii.ascii :=
  Ascii.Ascii (imported_to_bool (Imported.a____at___U_original__U2_lf_dot_U_imp__U2_lf__U_imp__no____whiles____eqv__iso__hyg28 a))
              (imported_to_bool (Imported.a____at___U_original__U2_lf_dot_U_imp__U2_lf__U_imp__no____whiles____eqv__iso__hyg30 a))
              (imported_to_bool (Imported.a____at___U_original__U2_lf_dot_U_imp__U2_lf__U_imp__no____whiles____eqv__iso__hyg32 a))
              (imported_to_bool (Imported.a____at___U_original__U2_lf_dot_U_imp__U2_lf__U_imp__no____whiles____eqv__iso__hyg34 a))
              (imported_to_bool (Imported.a____at___U_original__U2_lf_dot_U_imp__U2_lf__U_imp__no____whiles____eqv__iso__hyg36 a))
              (imported_to_bool (Imported.a____at___U_original__U2_lf_dot_U_imp__U2_lf__U_imp__no____whiles____eqv__iso__hyg38 a))
              (imported_to_bool (Imported.a____at___U_original__U2_lf_dot_U_imp__U2_lf__U_imp__no____whiles____eqv__iso__hyg40 a))
              (imported_to_bool (Imported.a____at___U_original__U2_lf_dot_U_imp__U2_lf__U_imp__no____whiles____eqv__iso__hyg42 a)).

Lemma ascii_roundtrip1 : forall a, imported_to_ascii (ascii_to_imported a) = a.
Proof.
  intros [b0 b1 b2 b3 b4 b5 b6 b7]. simpl.
  destruct b0, b1, b2, b3, b4, b5, b6, b7; reflexivity.
Qed.

Lemma bool_roundtrip : forall b : Imported.mybool, bool_to_imported (imported_to_bool b) = b.
Proof. intros []; reflexivity. Qed.

Lemma ascii_roundtrip2 : forall a, ascii_to_imported (imported_to_ascii a) = a.
Proof.
  intro a.
  set (b0 := Imported.a____at___U_original__U2_lf_dot_U_imp__U2_lf__U_imp__no____whiles____eqv__iso__hyg28 a).
  set (b1 := Imported.a____at___U_original__U2_lf_dot_U_imp__U2_lf__U_imp__no____whiles____eqv__iso__hyg30 a).
  set (b2 := Imported.a____at___U_original__U2_lf_dot_U_imp__U2_lf__U_imp__no____whiles____eqv__iso__hyg32 a).
  set (b3 := Imported.a____at___U_original__U2_lf_dot_U_imp__U2_lf__U_imp__no____whiles____eqv__iso__hyg34 a).
  set (b4 := Imported.a____at___U_original__U2_lf_dot_U_imp__U2_lf__U_imp__no____whiles____eqv__iso__hyg36 a).
  set (b5 := Imported.a____at___U_original__U2_lf_dot_U_imp__U2_lf__U_imp__no____whiles____eqv__iso__hyg38 a).
  set (b6 := Imported.a____at___U_original__U2_lf_dot_U_imp__U2_lf__U_imp__no____whiles____eqv__iso__hyg40 a).
  set (b7 := Imported.a____at___U_original__U2_lf_dot_U_imp__U2_lf__U_imp__no____whiles____eqv__iso__hyg42 a).
  (* Due to eta for primitive projections, a = myascii_Ascii b0 b1 b2 b3 b4 b5 b6 b7 definitionally *)
  change a with (Imported.myascii_Ascii b0 b1 b2 b3 b4 b5 b6 b7).
  unfold imported_to_ascii, ascii_to_imported. simpl.
  subst b0 b1 b2 b3 b4 b5 b6 b7.
  destruct (Imported.a____at___U_original__U2_lf_dot_U_imp__U2_lf__U_imp__no____whiles____eqv__iso__hyg28 a),
           (Imported.a____at___U_original__U2_lf_dot_U_imp__U2_lf__U_imp__no____whiles____eqv__iso__hyg30 a),
           (Imported.a____at___U_original__U2_lf_dot_U_imp__U2_lf__U_imp__no____whiles____eqv__iso__hyg32 a),
           (Imported.a____at___U_original__U2_lf_dot_U_imp__U2_lf__U_imp__no____whiles____eqv__iso__hyg34 a),
           (Imported.a____at___U_original__U2_lf_dot_U_imp__U2_lf__U_imp__no____whiles____eqv__iso__hyg36 a),
           (Imported.a____at___U_original__U2_lf_dot_U_imp__U2_lf__U_imp__no____whiles____eqv__iso__hyg38 a),
           (Imported.a____at___U_original__U2_lf_dot_U_imp__U2_lf__U_imp__no____whiles____eqv__iso__hyg40 a),
           (Imported.a____at___U_original__U2_lf_dot_U_imp__U2_lf__U_imp__no____whiles____eqv__iso__hyg42 a); 
  reflexivity.
Qed.

(* string isomorphism *)
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

Lemma string_roundtrip1 : forall s, imported_to_string (string_to_imported s) = s.
Proof.
  induction s; simpl.
  - reflexivity.
  - f_equal. apply ascii_roundtrip1. apply IHs.
Qed.

Lemma string_roundtrip2 : forall s, string_to_imported (imported_to_string s) = s.
Proof.
  induction s; simpl.
  - reflexivity.
  - f_equal. apply ascii_roundtrip2. apply IHs.
Qed.

Instance String_string_iso : Iso String.string imported_String_string.
Proof.
  exists string_to_imported imported_to_string.
  - intro s. rewrite string_roundtrip2. exact IsomorphismDefinitions.eq_refl.
  - intro s. rewrite string_roundtrip1. exact IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant String.string := {}.
Instance: KnownConstant Imported.String_string := {}.
Instance: IsoStatementProofFor String.string String_string_iso := {}.
Instance: IsoStatementProofBetween String.string Imported.String_string String_string_iso := {}.
