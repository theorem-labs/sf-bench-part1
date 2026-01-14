From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

Definition imported_String_string : Type := Imported.String_string.

(* mybool <-> bool *)
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

(* ascii <-> Ascii_ascii *)
Definition ascii_to_lean (a : Ascii.ascii) : Imported.Ascii_ascii :=
  match a with
  | Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
      Imported.Ascii_ascii_Ascii
        (bool_to_mybool b0) (bool_to_mybool b1) (bool_to_mybool b2) (bool_to_mybool b3)
        (bool_to_mybool b4) (bool_to_mybool b5) (bool_to_mybool b6) (bool_to_mybool b7)
  end.

Definition lean_to_ascii (a : Imported.Ascii_ascii) : Ascii.ascii :=
  Ascii.Ascii 
    (mybool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__while____continue__iso__hyg28 a))
    (mybool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__while____continue__iso__hyg30 a))
    (mybool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__while____continue__iso__hyg32 a))
    (mybool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__while____continue__iso__hyg34 a))
    (mybool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__while____continue__iso__hyg36 a))
    (mybool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__while____continue__iso__hyg38 a))
    (mybool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__while____continue__iso__hyg40 a))
    (mybool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__while____continue__iso__hyg42 a)).

(* string <-> String_string *)
Fixpoint string_to_lean (s : String.string) : imported_String_string :=
  match s with
  | String.EmptyString => Imported.String_string_EmptyString
  | String.String a s' => Imported.String_string_String (ascii_to_lean a) (string_to_lean s')
  end.

Fixpoint lean_to_string (s : imported_String_string) : String.string :=
  match s with
  | Imported.String_string_EmptyString => String.EmptyString
  | Imported.String_string_String a s' => String.String (lean_to_ascii a) (lean_to_string s')
  end.

Lemma mybool_roundtrip1 : forall b, mybool_to_bool (bool_to_mybool b) = b.
Proof. destruct b; reflexivity. Qed.

Lemma mybool_roundtrip2 : forall b, bool_to_mybool (mybool_to_bool b) = b.
Proof. destruct b; reflexivity. Qed.

Lemma ascii_roundtrip1 : forall a, lean_to_ascii (ascii_to_lean a) = a.
Proof. 
  destruct a. unfold ascii_to_lean, lean_to_ascii. cbn.
  f_equal; apply mybool_roundtrip1.
Qed.

Lemma ascii_roundtrip2 : forall a, ascii_to_lean (lean_to_ascii a) = a.
Proof. 
  intro a. destruct a.
  unfold lean_to_ascii, ascii_to_lean. cbn.
  f_equal; apply mybool_roundtrip2.
Qed.

Lemma string_roundtrip1 : forall s, lean_to_string (string_to_lean s) = s.
Proof.
  induction s; simpl.
  - reflexivity.
  - f_equal. apply ascii_roundtrip1. apply IHs.
Qed.

Lemma string_roundtrip2 : forall s, string_to_lean (lean_to_string s) = s.
Proof.
  induction s; simpl.
  - reflexivity.
  - f_equal. apply ascii_roundtrip2. apply IHs.
Qed.

Instance String_string_iso : Iso String.string imported_String_string.
Proof.
  refine {| to := string_to_lean; from := lean_to_string |}.
  - intro x. 
    pose proof (string_roundtrip2 x) as H.
    rewrite H. exact IsomorphismDefinitions.eq_refl.
  - intro x.
    pose proof (string_roundtrip1 x) as H.
    rewrite H. exact IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant String.string := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.String_string := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor String.string String_string_iso := {}.
Instance: IsoStatementProofBetween String.string Imported.String_string String_string_iso := {}.
