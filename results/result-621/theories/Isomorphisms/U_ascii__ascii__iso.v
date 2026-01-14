From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

From IsomorphismChecker Require Export Isomorphisms.bool__iso.

Definition imported_Ascii_ascii : Type := Imported.ascii.

(* Use the same definitions from U_string__string__iso *)
Definition ascii_to_imported (a : Ascii.ascii) : Imported.ascii :=
  match a with
  | Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    Imported.ascii_Ascii (bool_to_imported b0) (bool_to_imported b1) (bool_to_imported b2) (bool_to_imported b3)
                         (bool_to_imported b4) (bool_to_imported b5) (bool_to_imported b6) (bool_to_imported b7)
  end.

Definition imported_to_ascii (a : Imported.ascii) : Ascii.ascii :=
  Ascii.Ascii 
    (imported_to_bool (Imported.a____at___U_original__U2_lf_dot_U_maps__U2_lf__U_maps__examplepmap__iso__hyg28 a))
    (imported_to_bool (Imported.a____at___U_original__U2_lf_dot_U_maps__U2_lf__U_maps__examplepmap__iso__hyg30 a))
    (imported_to_bool (Imported.a____at___U_original__U2_lf_dot_U_maps__U2_lf__U_maps__examplepmap__iso__hyg32 a))
    (imported_to_bool (Imported.a____at___U_original__U2_lf_dot_U_maps__U2_lf__U_maps__examplepmap__iso__hyg34 a))
    (imported_to_bool (Imported.a____at___U_original__U2_lf_dot_U_maps__U2_lf__U_maps__examplepmap__iso__hyg36 a))
    (imported_to_bool (Imported.a____at___U_original__U2_lf_dot_U_maps__U2_lf__U_maps__examplepmap__iso__hyg38 a))
    (imported_to_bool (Imported.a____at___U_original__U2_lf_dot_U_maps__U2_lf__U_maps__examplepmap__iso__hyg40 a))
    (imported_to_bool (Imported.a____at___U_original__U2_lf_dot_U_maps__U2_lf__U_maps__examplepmap__iso__hyg42 a)).

Lemma ascii_roundtrip : forall a, IsomorphismDefinitions.eq (imported_to_ascii (ascii_to_imported a)) a.
Proof.
  intros [b0 b1 b2 b3 b4 b5 b6 b7].
  unfold ascii_to_imported, imported_to_ascii. simpl.
  unfold bool_to_imported, imported_to_bool.
  destruct b0, b1, b2, b3, b4, b5, b6, b7; exact IsomorphismDefinitions.eq_refl.
Qed.

Lemma imported_ascii_roundtrip : forall a, IsomorphismDefinitions.eq (ascii_to_imported (imported_to_ascii a)) a.
Proof.
  intros a. destruct a as [b0 b1 b2 b3 b4 b5 b6 b7].
  unfold imported_to_ascii, ascii_to_imported. simpl.
  unfold bool_to_imported, imported_to_bool.
  destruct b0, b1, b2, b3, b4, b5, b6, b7; exact IsomorphismDefinitions.eq_refl.
Qed.

Instance Ascii_ascii_iso : Iso Ascii.ascii imported_Ascii_ascii :=
  Build_Iso ascii_to_imported imported_to_ascii imported_ascii_roundtrip ascii_roundtrip.

Instance: KnownConstant Ascii.ascii := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.ascii := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Ascii.ascii Ascii_ascii_iso := {}.
Instance: IsoStatementProofBetween Ascii.ascii Imported.ascii Ascii_ascii_iso := {}.
