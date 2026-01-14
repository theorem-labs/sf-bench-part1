From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

(* First we need an isomorphism between bool and Imported.mybool *)
Definition bool_to_mybool (b : Datatypes.bool) : Imported.mybool :=
  match b with
  | Datatypes.true => Imported.mybool_mytrue
  | Datatypes.false => Imported.mybool_myfalse
  end.

Definition mybool_to_bool (b : Imported.mybool) : Datatypes.bool :=
  match b with
  | Imported.mybool_mytrue => Datatypes.true
  | Imported.mybool_myfalse => Datatypes.false
  end.

Lemma bool_mybool_to_from : forall x, IsomorphismDefinitions.eq (bool_to_mybool (mybool_to_bool x)) x.
Proof.
  intros []; apply IsomorphismDefinitions.eq_refl.
Qed.

Lemma bool_mybool_from_to : forall x, IsomorphismDefinitions.eq (mybool_to_bool (bool_to_mybool x)) x.
Proof.
  intros []; apply IsomorphismDefinitions.eq_refl.
Qed.

Definition bool_mybool_iso : Iso Datatypes.bool Imported.mybool :=
  Build_Iso bool_to_mybool mybool_to_bool bool_mybool_to_from bool_mybool_from_to.

(* Now the isomorphism between Ascii.ascii and Imported.Ascii_ascii *)
Definition ascii_to_imported (a : Ascii.ascii) : Imported.Ascii_ascii :=
  match a with
  | Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    Imported.Ascii_ascii_Ascii 
      (bool_to_mybool b0)
      (bool_to_mybool b1)
      (bool_to_mybool b2)
      (bool_to_mybool b3)
      (bool_to_mybool b4)
      (bool_to_mybool b5)
      (bool_to_mybool b6)
      (bool_to_mybool b7)
  end.

Definition imported_to_ascii (a : Imported.Ascii_ascii) : Ascii.ascii :=
  Ascii.Ascii
    (mybool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__test____der2__iso__hyg14 a))
    (mybool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__test____der2__iso__hyg16 a))
    (mybool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__test____der2__iso__hyg18 a))
    (mybool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__test____der2__iso__hyg20 a))
    (mybool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__test____der2__iso__hyg22 a))
    (mybool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__test____der2__iso__hyg24 a))
    (mybool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__test____der2__iso__hyg26 a))
    (mybool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__test____der2__iso__hyg28 a)).

Lemma ascii_to_from : forall x, IsomorphismDefinitions.eq (ascii_to_imported (imported_to_ascii x)) x.
Proof.
  intros x.
  destruct x as [b0 b1 b2 b3 b4 b5 b6 b7].
  unfold imported_to_ascii, ascii_to_imported.
  simpl.
  destruct b0, b1, b2, b3, b4, b5, b6, b7; apply IsomorphismDefinitions.eq_refl.
Qed.

Lemma ascii_from_to : forall x, IsomorphismDefinitions.eq (imported_to_ascii (ascii_to_imported x)) x.
Proof.
  intros [b0 b1 b2 b3 b4 b5 b6 b7].
  unfold imported_to_ascii, ascii_to_imported.
  simpl.
  destruct b0, b1, b2, b3, b4, b5, b6, b7; apply IsomorphismDefinitions.eq_refl.
Qed.

Definition imported_Ascii_ascii : Type := Imported.Ascii_ascii.
Instance Ascii_ascii_iso : Iso Ascii.ascii imported_Ascii_ascii :=
  Build_Iso ascii_to_imported imported_to_ascii ascii_to_from ascii_from_to.
Instance: KnownConstant Ascii.ascii := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Ascii_ascii := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Ascii.ascii Ascii_ascii_iso := {}.
Instance: IsoStatementProofBetween Ascii.ascii Imported.Ascii_ascii Ascii_ascii_iso := {}.