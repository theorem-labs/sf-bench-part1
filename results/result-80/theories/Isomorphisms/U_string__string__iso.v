From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

(* Shorter notation for projections *)
Local Notation p13 := Imported.a____at___U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_w__iso__hyg13.
Local Notation p15 := Imported.a____at___U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_w__iso__hyg15.
Local Notation p17 := Imported.a____at___U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_w__iso__hyg17.
Local Notation p19 := Imported.a____at___U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_w__iso__hyg19.
Local Notation p21 := Imported.a____at___U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_w__iso__hyg21.
Local Notation p23 := Imported.a____at___U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_w__iso__hyg23.
Local Notation p25 := Imported.a____at___U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_w__iso__hyg25.
Local Notation p27 := Imported.a____at___U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_w__iso__hyg27.

(* First, isomorphism for bool *)
Definition bool_to_imported (b : bool) : Imported.Mybool :=
  match b with
  | true => Imported.Mybool_true
  | false => Imported.Mybool_false
  end.

Definition imported_to_bool (b : Imported.Mybool) : bool :=
  match b with
  | Imported.Mybool_true => true
  | Imported.Mybool_false => false
  end.

Instance bool_iso : Iso bool Imported.Mybool.
Proof.
  apply (Build_Iso bool_to_imported imported_to_bool).
  - intro b. destruct b; apply IsomorphismDefinitions.eq_refl.
  - intro b. destruct b; apply IsomorphismDefinitions.eq_refl.
Defined.

(* Isomorphism for Ascii.ascii *)
Definition ascii_to_imported (a : Ascii.ascii) : Imported.Ascii_ascii :=
  match a with
  | Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
      Imported.Ascii_ascii_Ascii
        (bool_to_imported b0) (bool_to_imported b1)
        (bool_to_imported b2) (bool_to_imported b3)
        (bool_to_imported b4) (bool_to_imported b5)
        (bool_to_imported b6) (bool_to_imported b7)
  end.

Definition imported_to_ascii (a : Imported.Ascii_ascii) : Ascii.ascii :=
  Ascii.Ascii
    (imported_to_bool (p13 a))
    (imported_to_bool (p15 a))
    (imported_to_bool (p17 a))
    (imported_to_bool (p19 a))
    (imported_to_bool (p21 a))
    (imported_to_bool (p23 a))
    (imported_to_bool (p25 a))
    (imported_to_bool (p27 a)).

Instance ascii_iso : Iso Ascii.ascii Imported.Ascii_ascii.
Proof.
  apply (Build_Iso ascii_to_imported imported_to_ascii).
  - intro a. destruct a as [b0 b1 b2 b3 b4 b5 b6 b7].
    simpl. destruct b0, b1, b2, b3, b4, b5, b6, b7; apply IsomorphismDefinitions.eq_refl.
  - intro a. destruct a as [f0 f1 f2 f3 f4 f5 f6 f7].
    simpl.
    destruct f0, f1, f2, f3, f4, f5, f6, f7;
    apply IsomorphismDefinitions.eq_refl.
Defined.

(* Isomorphism for String.string *)
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

Definition imported_String_string : Type := Imported.String_string.

Lemma string_roundtrip1 : forall s, IsomorphismDefinitions.eq (imported_to_string (string_to_imported s)) s.
Proof.
  fix IH 1.
  intro s. destruct s as [| c rest].
  - apply IsomorphismDefinitions.eq_refl.
  - simpl.
    destruct c as [b0 b1 b2 b3 b4 b5 b6 b7].
    destruct b0, b1, b2, b3, b4, b5, b6, b7; simpl.
    all: apply (IsoEq.f_equal (fun r => String.String _ r) (IH rest)).
Defined.

Lemma string_roundtrip2 : forall s, IsomorphismDefinitions.eq (string_to_imported (imported_to_string s)) s.
Proof.
  fix IH 1.
  intro s. destruct s as [| c rest].
  - apply IsomorphismDefinitions.eq_refl.
  - simpl. destruct c as [f0 f1 f2 f3 f4 f5 f6 f7].
    destruct f0, f1, f2, f3, f4, f5, f6, f7; simpl.
    all: apply (IsoEq.f_equal (fun r => Imported.String_string_String _ r) (IH rest)).
Defined.

Instance String_string_iso : Iso String.string imported_String_string.
Proof.
  apply (Build_Iso string_to_imported imported_to_string).
  - exact string_roundtrip2.
  - exact string_roundtrip1.
Defined.

Instance: KnownConstant String.string := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.String_string := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor String.string String_string_iso := {}.
Instance: IsoStatementProofBetween String.string Imported.String_string String_string_iso := {}.