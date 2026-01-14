From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From Stdlib Require Import Ascii.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_Ascii_ascii : Type := Imported.Ascii_ascii.

(* Bool isomorphism helper *)
Definition bool_to_imported (b : Datatypes.bool) : Imported.Bool' :=
  match b with
  | true => Imported.Bool'_true
  | false => Imported.Bool'_false
  end.

Definition bool_from_imported (b : Imported.Bool') : Datatypes.bool :=
  match b with
  | Imported.Bool'_true => true
  | Imported.Bool'_false => false
  end.

Lemma bool_to_from : forall b, bool_to_imported (bool_from_imported b) = b.
Proof. destruct b; reflexivity. Qed.

Lemma bool_from_to : forall b, bool_from_imported (bool_to_imported b) = b.
Proof. destruct b; reflexivity. Qed.

(* Ascii isomorphism *)
Definition ascii_to_imported (a : Ascii.ascii) : Imported.Ascii_ascii :=
  match a with
  | Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    Imported.Ascii_ascii_Ascii (bool_to_imported b0) (bool_to_imported b1) 
                      (bool_to_imported b2) (bool_to_imported b3)
                      (bool_to_imported b4) (bool_to_imported b5)
                      (bool_to_imported b6) (bool_to_imported b7)
  end.

Definition ascii_from_imported (a : Imported.Ascii_ascii) : Ascii.ascii :=
  Ascii.Ascii (bool_from_imported (Imported.a0 a))
              (bool_from_imported (Imported.a1 a))
              (bool_from_imported (Imported.a2 a))
              (bool_from_imported (Imported.a3 a))
              (bool_from_imported (Imported.a4 a))
              (bool_from_imported (Imported.a5 a))
              (bool_from_imported (Imported.a6 a))
              (bool_from_imported (Imported.a7 a)).

(* Helper lemmas *)
Lemma ascii_mk_eq : forall b0 b1 b2 b3 b4 b5 b6 b7 b0' b1' b2' b3' b4' b5' b6' b7' : Imported.Bool',
  @Logic.eq _ b0 b0' -> @Logic.eq _ b1 b1' -> @Logic.eq _ b2 b2' -> @Logic.eq _ b3 b3' ->
  @Logic.eq _ b4 b4' -> @Logic.eq _ b5 b5' -> @Logic.eq _ b6 b6' -> @Logic.eq _ b7 b7' ->
  @Logic.eq _ (Imported.Ascii_ascii_Ascii b0 b1 b2 b3 b4 b5 b6 b7) (Imported.Ascii_ascii_Ascii b0' b1' b2' b3' b4' b5' b6' b7').
Proof.
  intros.
  destruct H. destruct H0. destruct H1. destruct H2.
  destruct H3. destruct H4. destruct H5. destruct H6.
  reflexivity.
Qed.

Lemma coq_ascii_eq : forall b0 b1 b2 b3 b4 b5 b6 b7 b0' b1' b2' b3' b4' b5' b6' b7' : Datatypes.bool,
  @Logic.eq _ b0 b0' -> @Logic.eq _ b1 b1' -> @Logic.eq _ b2 b2' -> @Logic.eq _ b3 b3' ->
  @Logic.eq _ b4 b4' -> @Logic.eq _ b5 b5' -> @Logic.eq _ b6 b6' -> @Logic.eq _ b7 b7' ->
  @Logic.eq _ (Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7) (Ascii.Ascii b0' b1' b2' b3' b4' b5' b6' b7').
Proof.
  intros.
  destruct H. destruct H0. destruct H1. destruct H2.
  destruct H3. destruct H4. destruct H5. destruct H6.
  reflexivity.
Qed.

Lemma ascii_to_from : forall a, ascii_to_imported (ascii_from_imported a) = a.
Proof.
  intro a.
  unfold ascii_to_imported, ascii_from_imported. simpl.
  apply ascii_mk_eq; apply bool_to_from.
Qed.

Lemma ascii_from_to : forall a, ascii_from_imported (ascii_to_imported a) = a.
Proof.
  destruct a.
  unfold ascii_from_imported, ascii_to_imported. simpl.
  apply coq_ascii_eq; apply bool_from_to.
Qed.

(* Convert from Logic.eq to IsomorphismDefinitions.eq *)
Lemma logic_eq_to_iso_eq : forall (A : Type) (x y : A), @Logic.eq A x y -> IsomorphismDefinitions.eq x y.
Proof.
  intros A x y H. destruct H. apply IsomorphismDefinitions.eq_refl.
Qed.

Instance Ascii_ascii_iso : Iso Ascii.ascii imported_Ascii_ascii := {|
  to := ascii_to_imported;
  from := ascii_from_imported;
  to_from := fun x => logic_eq_to_iso_eq (ascii_to_from x);
  from_to := fun x => logic_eq_to_iso_eq (ascii_from_to x);
|}.

Instance: KnownConstant Ascii.ascii := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Ascii_ascii := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Ascii.ascii Ascii_ascii_iso := {}.
Instance: IsoStatementProofBetween Ascii.ascii Imported.Ascii_ascii Ascii_ascii_iso := {}.