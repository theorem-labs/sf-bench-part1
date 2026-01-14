From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

(* First, we need an isomorphism between Rocq's bool and Imported.mybool *)
Definition imported_mybool : Type := Imported.mybool.

Definition bool_to_mybool (b : bool) : imported_mybool :=
  match b with
  | true => Imported.mybool_mytrue
  | false => Imported.mybool_myfalse
  end.

Definition mybool_to_bool (b : imported_mybool) : bool :=
  Imported.mybool_recl (fun _ => bool) true false b.

Lemma mybool_to_from : forall x : imported_mybool,
  IsomorphismDefinitions.eq (bool_to_mybool (mybool_to_bool x)) x.
Proof.
  intro x.
  apply (Imported.mybool_indl (fun x => IsomorphismDefinitions.eq (bool_to_mybool (mybool_to_bool x)) x));
  apply IsomorphismDefinitions.eq_refl.
Qed.

Lemma mybool_from_to : forall x : bool,
  IsomorphismDefinitions.eq (mybool_to_bool (bool_to_mybool x)) x.
Proof.
  intro x. destruct x; apply IsomorphismDefinitions.eq_refl.
Qed.

Instance mybool_iso : Iso bool imported_mybool := {|
  to := bool_to_mybool;
  from := mybool_to_bool;
  to_from := mybool_to_from;
  from_to := mybool_from_to
|}.

(* Now define the ascii isomorphism *)
Definition imported_Ascii_ascii : Type := Imported.Ascii_ascii.

(* Convert from Rocq Ascii.ascii to Imported.Ascii_ascii *)
Definition ascii_to_imported (a : Ascii.ascii) : imported_Ascii_ascii :=
  match a with
  | Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    Imported.Ascii_Ascii
      (bool_to_mybool b0)
      (bool_to_mybool b1)
      (bool_to_mybool b2)
      (bool_to_mybool b3)
      (bool_to_mybool b4)
      (bool_to_mybool b5)
      (bool_to_mybool b6)
      (bool_to_mybool b7)
  end.

(* Convert from Imported.Ascii_ascii to Rocq Ascii.ascii *)
Definition imported_to_ascii (a : imported_Ascii_ascii) : Ascii.ascii :=
  Ascii.Ascii
    (mybool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__test____der6__iso__hyg63 a))
    (mybool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__test____der6__iso__hyg65 a))
    (mybool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__test____der6__iso__hyg67 a))
    (mybool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__test____der6__iso__hyg69 a))
    (mybool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__test____der6__iso__hyg71 a))
    (mybool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__test____der6__iso__hyg73 a))
    (mybool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__test____der6__iso__hyg75 a))
    (mybool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__test____der6__iso__hyg77 a)).

(* Helper for mybool path in Leibniz eq *)
Definition mybool_to_from_path (x : imported_mybool) :
  Logic.eq (bool_to_mybool (mybool_to_bool x)) x :=
  Imported.mybool_recl (fun x => Logic.eq (bool_to_mybool (mybool_to_bool x)) x) Logic.eq_refl Logic.eq_refl x.

(* Proof that to_from holds *)
Lemma ascii_to_from : forall x : imported_Ascii_ascii,
  IsomorphismDefinitions.eq (ascii_to_imported (imported_to_ascii x)) x.
Proof.
  intro x.
  apply (Imported.Ascii_ascii_indl (fun x => IsomorphismDefinitions.eq (ascii_to_imported (imported_to_ascii x)) x)).
  intros b0 b1 b2 b3 b4 b5 b6 b7.
  unfold imported_to_ascii, ascii_to_imported. simpl.
  rewrite (mybool_to_from_path b0).
  rewrite (mybool_to_from_path b1).
  rewrite (mybool_to_from_path b2).
  rewrite (mybool_to_from_path b3).
  rewrite (mybool_to_from_path b4).
  rewrite (mybool_to_from_path b5).
  rewrite (mybool_to_from_path b6).
  rewrite (mybool_to_from_path b7).
  apply IsomorphismDefinitions.eq_refl.
Qed.

(* Proof that from_to holds *)
Lemma ascii_from_to : forall x : Ascii.ascii,
  IsomorphismDefinitions.eq (imported_to_ascii (ascii_to_imported x)) x.
Proof.
  intro x. destruct x as [b0 b1 b2 b3 b4 b5 b6 b7].
  unfold imported_to_ascii, ascii_to_imported. simpl.
  destruct b0, b1, b2, b3, b4, b5, b6, b7; apply IsomorphismDefinitions.eq_refl.
Qed.

Instance Ascii_ascii_iso : Iso Ascii.ascii imported_Ascii_ascii := {|
  to := ascii_to_imported;
  from := imported_to_ascii;
  to_from := ascii_to_from;
  from_to := ascii_from_to
|}.

Instance: KnownConstant Ascii.ascii := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Ascii_ascii := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Ascii.ascii Ascii_ascii_iso := {}.
Instance: IsoStatementProofBetween Ascii.ascii Imported.Ascii_ascii Ascii_ascii_iso := {}.
