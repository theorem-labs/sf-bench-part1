From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.
Require Import Stdlib.Strings.String.

(* First we need nat isomorphism *)
Fixpoint to_nat (n : Datatypes.nat) : Imported.nat :=
  match n with
  | Datatypes.O => Imported.nat_O
  | Datatypes.S n' => Imported.nat_S (to_nat n')
  end.

Fixpoint from_nat (n : Imported.nat) : Datatypes.nat :=
  match n with
  | Imported.nat_O => Datatypes.O
  | Imported.nat_S n' => Datatypes.S (from_nat n')
  end.

Lemma to_from_nat : forall n, eq (to_nat (from_nat n)) n.
Proof.
  fix to_from 1.
  intros n.
  destruct n; simpl.
  - apply eq_refl.
  - apply (IsoEq.f_equal Imported.nat_S). apply to_from.
Qed.

Lemma from_to_nat : forall n, eq (from_nat (to_nat n)) n.
Proof.
  fix from_to 1.
  intros n.
  destruct n; simpl.
  - apply eq_refl.
  - apply (IsoEq.f_equal Datatypes.S). apply from_to.
Qed.

Instance nat_iso_local : Iso Datatypes.nat Imported.nat :=
  {| to := to_nat; from := from_nat; to_from := to_from_nat; from_to := from_to_nat |}.

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

Instance bool_iso_local : Iso Datatypes.bool Imported.mybool :=
  {| to := to_bool; from := from_bool; to_from := to_from_bool; from_to := from_to_bool |}.

(* Need ascii isomorphism *)
Require Import Stdlib.Strings.Ascii.

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

Instance ascii_iso_local : Iso Ascii.ascii Imported.Ascii_ascii :=
  {| to := to_ascii; from := from_ascii; to_from := to_from_ascii; from_to := from_to_ascii |}.

(* Also need string isomorphism *)
Fixpoint to_string (s : string) : Imported.String_string :=
  match s with
  | EmptyString => Imported.String_string_EmptyString
  | String c s' => Imported.String_string_String (to_ascii c) (to_string s')
  end.

Fixpoint from_string (s : Imported.String_string) : string :=
  match s with
  | Imported.String_string_EmptyString => EmptyString
  | Imported.String_string_String c s' => String (from_ascii c) (from_string s')
  end.

Lemma to_from_string : forall s, eq (to_string (from_string s)) s.
Proof.
  fix to_from 1.
  intros s.
  destruct s; simpl.
  - apply eq_refl.
  - apply (IsoEq.f_equal2 Imported.String_string_String).
    + apply to_from_ascii.
    + apply to_from.
Qed.

Lemma from_to_string : forall s, eq (from_string (to_string s)) s.
Proof.
  fix from_to 1.
  intros s.
  destruct s; simpl.
  - apply eq_refl.
  - apply (IsoEq.f_equal2 String).
    + apply from_to_ascii.
    + apply from_to.
Qed.

Instance string_iso_local : Iso string Imported.String_string :=
  {| to := to_string; from := from_string; to_from := to_from_string; from_to := from_to_string |}.

Definition imported_Original_LF__DOT__Imp_LF_Imp_aexp : Type := Imported.Original_LF__DOT__Imp_LF_Imp_aexp.

(* Define aexp_to_imported and aexp_from_imported for use by other proofs *)
Fixpoint aexp_to_imported (a : Original.LF_DOT_Imp.LF.Imp.aexp) : imported_Original_LF__DOT__Imp_LF_Imp_aexp :=
  match a with
  | Original.LF_DOT_Imp.LF.Imp.ANum n => Imported.Original_LF__DOT__Imp_LF_Imp_aexp_ANum (to_nat n)
  | Original.LF_DOT_Imp.LF.Imp.AId x => Imported.Original_LF__DOT__Imp_LF_Imp_aexp_AId (to_string x)
  | Original.LF_DOT_Imp.LF.Imp.APlus a1 a2 => Imported.Original_LF__DOT__Imp_LF_Imp_aexp_APlus (aexp_to_imported a1) (aexp_to_imported a2)
  | Original.LF_DOT_Imp.LF.Imp.AMinus a1 a2 => Imported.Original_LF__DOT__Imp_LF_Imp_aexp_AMinus (aexp_to_imported a1) (aexp_to_imported a2)
  | Original.LF_DOT_Imp.LF.Imp.AMult a1 a2 => Imported.Original_LF__DOT__Imp_LF_Imp_aexp_AMult (aexp_to_imported a1) (aexp_to_imported a2)
  end.

Fixpoint aexp_from_imported (a : imported_Original_LF__DOT__Imp_LF_Imp_aexp) : Original.LF_DOT_Imp.LF.Imp.aexp :=
  match a with
  | Imported.Original_LF__DOT__Imp_LF_Imp_aexp_ANum n => Original.LF_DOT_Imp.LF.Imp.ANum (from_nat n)
  | Imported.Original_LF__DOT__Imp_LF_Imp_aexp_AId x => Original.LF_DOT_Imp.LF.Imp.AId (from_string x)
  | Imported.Original_LF__DOT__Imp_LF_Imp_aexp_APlus a1 a2 => Original.LF_DOT_Imp.LF.Imp.APlus (aexp_from_imported a1) (aexp_from_imported a2)
  | Imported.Original_LF__DOT__Imp_LF_Imp_aexp_AMinus a1 a2 => Original.LF_DOT_Imp.LF.Imp.AMinus (aexp_from_imported a1) (aexp_from_imported a2)
  | Imported.Original_LF__DOT__Imp_LF_Imp_aexp_AMult a1 a2 => Original.LF_DOT_Imp.LF.Imp.AMult (aexp_from_imported a1) (aexp_from_imported a2)
  end.

Lemma aexp_to_from : forall a, eq (aexp_to_imported (aexp_from_imported a)) a.
Proof.
  fix to_from 1.
  intros a.
  destruct a; simpl.
  + apply (IsoEq.f_equal Imported.Original_LF__DOT__Imp_LF_Imp_aexp_ANum). apply to_from_nat.
  + apply (IsoEq.f_equal Imported.Original_LF__DOT__Imp_LF_Imp_aexp_AId). apply to_from_string.
  + apply (IsoEq.f_equal2 Imported.Original_LF__DOT__Imp_LF_Imp_aexp_APlus); apply to_from.
  + apply (IsoEq.f_equal2 Imported.Original_LF__DOT__Imp_LF_Imp_aexp_AMinus); apply to_from.
  + apply (IsoEq.f_equal2 Imported.Original_LF__DOT__Imp_LF_Imp_aexp_AMult); apply to_from.
Qed.

Lemma aexp_from_to : forall a, eq (aexp_from_imported (aexp_to_imported a)) a.
Proof.
  fix from_to 1.
  intros a.
  destruct a; simpl.
  + apply (IsoEq.f_equal Original.LF_DOT_Imp.LF.Imp.ANum). apply from_to_nat.
  + apply (IsoEq.f_equal Original.LF_DOT_Imp.LF.Imp.AId). apply from_to_string.
  + apply (IsoEq.f_equal2 Original.LF_DOT_Imp.LF.Imp.APlus); apply from_to.
  + apply (IsoEq.f_equal2 Original.LF_DOT_Imp.LF.Imp.AMinus); apply from_to.
  + apply (IsoEq.f_equal2 Original.LF_DOT_Imp.LF.Imp.AMult); apply from_to.
Qed.

Instance Original_LF__DOT__Imp_LF_Imp_aexp_iso : Iso Original.LF_DOT_Imp.LF.Imp.aexp imported_Original_LF__DOT__Imp_LF_Imp_aexp :=
  {| to := aexp_to_imported; from := aexp_from_imported; to_from := aexp_to_from; from_to := aexp_from_to |}.

Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.aexp := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_aexp := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.aexp Original_LF__DOT__Imp_LF_Imp_aexp_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.aexp Imported.Original_LF__DOT__Imp_LF_Imp_aexp Original_LF__DOT__Imp_LF_Imp_aexp_iso := {}.
