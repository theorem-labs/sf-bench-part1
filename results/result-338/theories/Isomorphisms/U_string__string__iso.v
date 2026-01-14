From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

(* Bool isomorphism *)
Definition bool_to (b : Datatypes.bool) : Imported.Datatypes_bool :=
  match b with
  | Datatypes.true => Imported.Datatypes_bool_true
  | Datatypes.false => Imported.Datatypes_bool_false
  end.

Definition bool_from (b : Imported.Datatypes_bool) : Datatypes.bool :=
  match b with
  | Imported.Datatypes_bool_true => Datatypes.true
  | Imported.Datatypes_bool_false => Datatypes.false
  end.

Lemma bool_to_from : forall b, IsomorphismDefinitions.eq (bool_to (bool_from b)) b.
Proof.
  intros []; apply IsomorphismDefinitions.eq_refl.
Defined.

Lemma bool_from_to : forall b, IsomorphismDefinitions.eq (bool_from (bool_to b)) b.
Proof.
  intros []; apply IsomorphismDefinitions.eq_refl.
Defined.

Definition bool_iso : Iso Datatypes.bool Imported.Datatypes_bool :=
  Build_Iso bool_to bool_from bool_to_from bool_from_to.

(* Ascii isomorphism *)
Definition ascii_to (a : Ascii.ascii) : Imported.Ascii_ascii :=
  match a with
  | Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    Imported.Ascii_ascii_Ascii (bool_to b0) (bool_to b1) (bool_to b2) (bool_to b3)
                               (bool_to b4) (bool_to b5) (bool_to b6) (bool_to b7)
  end.

(* Shorter names for projections *)
Local Notation proj0 := Imported.a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____fold____map__iso__hyg35.
Local Notation proj1 := Imported.a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____fold____map__iso__hyg37.
Local Notation proj2 := Imported.a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____fold____map__iso__hyg39.
Local Notation proj3 := Imported.a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____fold____map__iso__hyg41.
Local Notation proj4 := Imported.a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____fold____map__iso__hyg43.
Local Notation proj5 := Imported.a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____fold____map__iso__hyg45.
Local Notation proj6 := Imported.a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____fold____map__iso__hyg47.
Local Notation proj7 := Imported.a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____fold____map__iso__hyg49.

Definition ascii_from (a : Imported.Ascii_ascii) : Ascii.ascii :=
  Ascii.Ascii (bool_from (proj0 a)) (bool_from (proj1 a)) 
              (bool_from (proj2 a)) (bool_from (proj3 a))
              (bool_from (proj4 a)) (bool_from (proj5 a)) 
              (bool_from (proj6 a)) (bool_from (proj7 a)).

Lemma ascii_to_from : forall a, IsomorphismDefinitions.eq (ascii_to (ascii_from a)) a.
Proof.
  intro a.
  destruct a.
  simpl.
  destruct a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____fold____map__iso__hyg35,
           a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____fold____map__iso__hyg37,
           a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____fold____map__iso__hyg39,
           a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____fold____map__iso__hyg41,
           a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____fold____map__iso__hyg43,
           a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____fold____map__iso__hyg45,
           a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____fold____map__iso__hyg47,
           a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____fold____map__iso__hyg49.
  all: simpl; apply IsomorphismDefinitions.eq_refl.
Defined.

Lemma ascii_from_to : forall a, IsomorphismDefinitions.eq (ascii_from (ascii_to a)) a.
Proof.
  intros [b0 b1 b2 b3 b4 b5 b6 b7]. simpl.
  destruct b0, b1, b2, b3, b4, b5, b6, b7.
  all: simpl; apply IsomorphismDefinitions.eq_refl.
Defined.

Definition ascii_iso : Iso Ascii.ascii Imported.Ascii_ascii :=
  Build_Iso ascii_to ascii_from ascii_to_from ascii_from_to.

(* String isomorphism *)
Definition imported_String_string : Type := Imported.String_string.

Fixpoint string_to (s : String.string) : Imported.String_string :=
  match s with
  | String.EmptyString => Imported.String_string_EmptyString
  | String.String a s' => Imported.String_string_String (ascii_to a) (string_to s')
  end.

Fixpoint string_from (s : Imported.String_string) : String.string :=
  match s with
  | Imported.String_string_EmptyString => String.EmptyString
  | Imported.String_string_String a s' => String.String (ascii_from a) (string_from s')
  end.

Lemma string_to_from : forall s, IsomorphismDefinitions.eq (string_to (string_from s)) s.
Proof.
  fix IH 1. intros [|a s'].
  - apply IsomorphismDefinitions.eq_refl.
  - simpl. apply IsoEq.f_equal2. apply ascii_to_from. apply IH.
Defined.

Lemma string_from_to : forall s, IsomorphismDefinitions.eq (string_from (string_to s)) s.
Proof.
  fix IH 1. intros [|a s'].
  - apply IsomorphismDefinitions.eq_refl.
  - simpl. apply IsoEq.f_equal2. apply ascii_from_to. apply IH.
Defined.

Instance String_string_iso : Iso String.string imported_String_string :=
  Build_Iso string_to string_from string_to_from string_from_to.

Instance: KnownConstant String.string := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.String_string := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor String.string String_string_iso := {}.
Instance: IsoStatementProofBetween String.string Imported.String_string String_string_iso := {}.