From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

(* Bool isomorphism *)
Definition bool_to_imported (b : Datatypes.bool) : Imported.Bool :=
  match b with
  | Datatypes.true => Imported.Bool_true
  | Datatypes.false => Imported.Bool_false
  end.

Definition bool_from_imported (b : Imported.Bool) : Datatypes.bool :=
  match b with
  | Imported.Bool_true => Datatypes.true
  | Imported.Bool_false => Datatypes.false
  end.

(* ascii isomorphism *)
Definition ascii_to_imported (a : Ascii.ascii) : Imported.ascii :=
  match a with
  | Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    Imported.ascii_Ascii (bool_to_imported b0) (bool_to_imported b1) 
                          (bool_to_imported b2) (bool_to_imported b3)
                          (bool_to_imported b4) (bool_to_imported b5)
                          (bool_to_imported b6) (bool_to_imported b7)
  end.

Definition ascii_from_imported (a : Imported.ascii) : Ascii.ascii :=
  Ascii.Ascii (bool_from_imported (Imported.a____at___U_original__U2_lf_dot_U_logic__U2_lf__U_logic__manual____grade____for____not____U3_pnp____informal__iso__hyg20 a))
              (bool_from_imported (Imported.a____at___U_original__U2_lf_dot_U_logic__U2_lf__U_logic__manual____grade____for____not____U3_pnp____informal__iso__hyg22 a))
              (bool_from_imported (Imported.a____at___U_original__U2_lf_dot_U_logic__U2_lf__U_logic__manual____grade____for____not____U3_pnp____informal__iso__hyg24 a))
              (bool_from_imported (Imported.a____at___U_original__U2_lf_dot_U_logic__U2_lf__U_logic__manual____grade____for____not____U3_pnp____informal__iso__hyg26 a))
              (bool_from_imported (Imported.a____at___U_original__U2_lf_dot_U_logic__U2_lf__U_logic__manual____grade____for____not____U3_pnp____informal__iso__hyg28 a))
              (bool_from_imported (Imported.a____at___U_original__U2_lf_dot_U_logic__U2_lf__U_logic__manual____grade____for____not____U3_pnp____informal__iso__hyg30 a))
              (bool_from_imported (Imported.a____at___U_original__U2_lf_dot_U_logic__U2_lf__U_logic__manual____grade____for____not____U3_pnp____informal__iso__hyg32 a))
              (bool_from_imported (Imported.a____at___U_original__U2_lf_dot_U_logic__U2_lf__U_logic__manual____grade____for____not____U3_pnp____informal__iso__hyg34 a)).

Definition imported_String_string : Type := Imported.String_string.

Fixpoint string_to_imported (s : String.string) : imported_String_string :=
  match s with
  | String.EmptyString => Imported.String_string_EmptyString
  | String.String a s' => Imported.String_string_String (ascii_to_imported a) (string_to_imported s')
  end.

Fixpoint string_from_imported (s : imported_String_string) : String.string :=
  match s with
  | Imported.String_string_EmptyString => String.EmptyString
  | Imported.String_string_String a s' => String.String (ascii_from_imported a) (string_from_imported s')
  end.

Lemma bool_to_from : forall b, bool_to_imported (bool_from_imported b) = b.
Proof.
  intro b; destruct b; reflexivity.
Qed.

Lemma bool_from_to : forall b, bool_from_imported (bool_to_imported b) = b.
Proof.
  intro b; destruct b; reflexivity.
Qed.

(* For records with primitive projections and eta, we use destruct on the Imported.ascii record *)
Lemma ascii_to_from : forall a : Imported.ascii, ascii_to_imported (ascii_from_imported a) = a.
Proof.
  intro a.
  destruct a as [b0 b1 b2 b3 b4 b5 b6 b7].
  simpl.
  destruct b0; destruct b1; destruct b2; destruct b3;
  destruct b4; destruct b5; destruct b6; destruct b7;
  reflexivity.
Qed.

Lemma ascii_from_to : forall a, ascii_from_imported (ascii_to_imported a) = a.
Proof.
  intro a; destruct a as [b0 b1 b2 b3 b4 b5 b6 b7]; simpl.
  destruct b0; destruct b1; destruct b2; destruct b3;
  destruct b4; destruct b5; destruct b6; destruct b7;
  reflexivity.
Qed.

Instance String_string_iso : Iso String.string imported_String_string.
Proof.
  unshelve eapply Build_Iso.
  - exact string_to_imported.
  - exact string_from_imported.
  - intro s.
    induction s as [|a s' IH].
    + apply IsomorphismDefinitions.eq_refl.
    + simpl.
      change (Imported.ascii_Ascii
          (bool_to_imported
             (bool_from_imported
                (Imported.a____at___U_original__U2_lf_dot_U_logic__U2_lf__U_logic__manual____grade____for____not____U3_pnp____informal__iso__hyg20
                   a)))
          (bool_to_imported
             (bool_from_imported
                (Imported.a____at___U_original__U2_lf_dot_U_logic__U2_lf__U_logic__manual____grade____for____not____U3_pnp____informal__iso__hyg22
                   a)))
          (bool_to_imported
             (bool_from_imported
                (Imported.a____at___U_original__U2_lf_dot_U_logic__U2_lf__U_logic__manual____grade____for____not____U3_pnp____informal__iso__hyg24
                   a)))
          (bool_to_imported
             (bool_from_imported
                (Imported.a____at___U_original__U2_lf_dot_U_logic__U2_lf__U_logic__manual____grade____for____not____U3_pnp____informal__iso__hyg26
                   a)))
          (bool_to_imported
             (bool_from_imported
                (Imported.a____at___U_original__U2_lf_dot_U_logic__U2_lf__U_logic__manual____grade____for____not____U3_pnp____informal__iso__hyg28
                   a)))
          (bool_to_imported
             (bool_from_imported
                (Imported.a____at___U_original__U2_lf_dot_U_logic__U2_lf__U_logic__manual____grade____for____not____U3_pnp____informal__iso__hyg30
                   a)))
          (bool_to_imported
             (bool_from_imported
                (Imported.a____at___U_original__U2_lf_dot_U_logic__U2_lf__U_logic__manual____grade____for____not____U3_pnp____informal__iso__hyg32
                   a)))
          (bool_to_imported
             (bool_from_imported
                (Imported.a____at___U_original__U2_lf_dot_U_logic__U2_lf__U_logic__manual____grade____for____not____U3_pnp____informal__iso__hyg34
                   a)))) with (ascii_to_imported (ascii_from_imported a)).
      rewrite ascii_to_from.
      apply IsoEq.f_equal.
      exact IH.
  - intro s.
    induction s as [|a s' IH].
    + apply IsomorphismDefinitions.eq_refl.
    + simpl. 
      rewrite ascii_from_to.
      apply IsoEq.f_equal.
      exact IH.
Defined.
Instance: KnownConstant String.string := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.String_string := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor String.string String_string_iso := {}.
Instance: IsoStatementProofBetween String.string Imported.String_string String_string_iso := {}.