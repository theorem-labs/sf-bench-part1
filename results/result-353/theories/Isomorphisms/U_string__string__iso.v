From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
From Stdlib Require Import Ascii String.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

(* First we need isomorphisms for bool and ascii *)

Definition bool_to_mybool (b : bool) : Imported.mybool :=
  match b with
  | true => Imported.mybool_true
  | false => Imported.mybool_false
  end.

Definition mybool_to_bool (b : Imported.mybool) : bool :=
  match b with
  | Imported.mybool_true => true
  | Imported.mybool_false => false
  end.

Lemma bool_mybool_to_from : forall b, IsomorphismDefinitions.eq (bool_to_mybool (mybool_to_bool b)) b.
Proof.
  intro b. destruct b; apply IsomorphismDefinitions.eq_refl.
Qed.

Lemma bool_mybool_from_to : forall b, IsomorphismDefinitions.eq (mybool_to_bool (bool_to_mybool b)) b.
Proof.
  intro b. destruct b; apply IsomorphismDefinitions.eq_refl.
Qed.

Instance bool_iso : Iso bool Imported.mybool.
Proof.
  exact (Build_Iso bool_to_mybool mybool_to_bool bool_mybool_to_from bool_mybool_from_to).
Defined.

Definition ascii_to_imported (a : ascii) : Imported.Ascii_ascii :=
  match a with
  | Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    Imported.Ascii_ascii_Ascii
      (bool_to_mybool b0) (bool_to_mybool b1) (bool_to_mybool b2) (bool_to_mybool b3)
      (bool_to_mybool b4) (bool_to_mybool b5) (bool_to_mybool b6) (bool_to_mybool b7)
  end.

Definition imported_to_ascii (a : Imported.Ascii_ascii) : ascii :=
  match a with
  | Imported.Ascii_ascii_Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    Ascii (mybool_to_bool b0) (mybool_to_bool b1) (mybool_to_bool b2) (mybool_to_bool b3)
          (mybool_to_bool b4) (mybool_to_bool b5) (mybool_to_bool b6) (mybool_to_bool b7)
  end.

Lemma ascii_to_from : forall a, IsomorphismDefinitions.eq (ascii_to_imported (imported_to_ascii a)) a.
Proof.
  intro a. destruct a.
  simpl.
  destruct a____at___U_original__U2_lf_dot_U_tactics__U2_lf__U_tactics__manual____grade____for____split____combine__iso__hyg28;
  destruct a____at___U_original__U2_lf_dot_U_tactics__U2_lf__U_tactics__manual____grade____for____split____combine__iso__hyg30;
  destruct a____at___U_original__U2_lf_dot_U_tactics__U2_lf__U_tactics__manual____grade____for____split____combine__iso__hyg32;
  destruct a____at___U_original__U2_lf_dot_U_tactics__U2_lf__U_tactics__manual____grade____for____split____combine__iso__hyg34;
  destruct a____at___U_original__U2_lf_dot_U_tactics__U2_lf__U_tactics__manual____grade____for____split____combine__iso__hyg36;
  destruct a____at___U_original__U2_lf_dot_U_tactics__U2_lf__U_tactics__manual____grade____for____split____combine__iso__hyg38;
  destruct a____at___U_original__U2_lf_dot_U_tactics__U2_lf__U_tactics__manual____grade____for____split____combine__iso__hyg40;
  destruct a____at___U_original__U2_lf_dot_U_tactics__U2_lf__U_tactics__manual____grade____for____split____combine__iso__hyg42;
  apply IsomorphismDefinitions.eq_refl.
Qed.

Lemma ascii_from_to : forall a, IsomorphismDefinitions.eq (imported_to_ascii (ascii_to_imported a)) a.
Proof.
  intro a. destruct a.
  simpl.
  destruct b; destruct b0; destruct b1; destruct b2;
  destruct b3; destruct b4; destruct b5; destruct b6;
  apply IsomorphismDefinitions.eq_refl.
Qed.

Instance ascii_iso : Iso ascii Imported.Ascii_ascii.
Proof.
  exact (Build_Iso ascii_to_imported imported_to_ascii ascii_to_from ascii_from_to).
Defined.

Definition imported_String_string : Type := Imported.String_string.

Fixpoint string_to_imported (s : string) : Imported.String_string :=
  match s with
  | EmptyString => Imported.String_string_EmptyString
  | String a s' => Imported.String_string_String (ascii_to_imported a) (string_to_imported s')
  end.

Fixpoint imported_to_string (s : Imported.String_string) : string :=
  match s with
  | Imported.String_string_EmptyString => EmptyString
  | Imported.String_string_String a s' => String (imported_to_ascii a) (imported_to_string s')
  end.

Lemma string_to_from : forall s, IsomorphismDefinitions.eq (string_to_imported (imported_to_string s)) s.
Proof.
  fix IH 1.
  intro s. destruct s as [|a s'].
  - apply IsomorphismDefinitions.eq_refl.
  - simpl.
    apply (IsoEq.f_equal2 Imported.String_string_String (ascii_to_from a) (IH s')).
Qed.

Lemma string_from_to : forall s, IsomorphismDefinitions.eq (imported_to_string (string_to_imported s)) s.
Proof.
  fix IH 1.
  intro s. destruct s as [|a s'].
  - apply IsomorphismDefinitions.eq_refl.
  - simpl.
    apply (IsoEq.f_equal2 String (ascii_from_to a) (IH s')).
Qed.

Instance String_string_iso : Iso String.string imported_String_string.
Proof.
  exact (Build_Iso string_to_imported imported_to_string string_to_from string_from_to).
Defined.

Instance: KnownConstant String.string := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.String_string := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor String.string String_string_iso := {}.
Instance: IsoStatementProofBetween String.string Imported.String_string String_string_iso := {}.