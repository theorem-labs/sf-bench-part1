From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
From IsomorphismChecker Require Export Isomorphisms.bool__iso.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

(* Imported.Ascii_ascii is an alias for Imported.Coqascii *)

Definition imported_Ascii_ascii : Type := Imported.Ascii_ascii.

(* Convert between Ascii.ascii and Imported.Coqascii *)
Definition ascii_to_coqascii (a : Ascii.ascii) : Imported.Coqascii :=
  match a with
  | Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    Imported.Coqascii_Ascii (bool_to_coqbool b0) (bool_to_coqbool b1) (bool_to_coqbool b2) (bool_to_coqbool b3)
                            (bool_to_coqbool b4) (bool_to_coqbool b5) (bool_to_coqbool b6) (bool_to_coqbool b7)
  end.

Definition coqascii_to_ascii (a : Imported.Coqascii) : Ascii.ascii :=
  Ascii.Ascii 
    (coqbool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_maps__U2_lf__U_maps__update____example2__iso__hyg23 a))
    (coqbool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_maps__U2_lf__U_maps__update____example2__iso__hyg25 a))
    (coqbool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_maps__U2_lf__U_maps__update____example2__iso__hyg27 a))
    (coqbool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_maps__U2_lf__U_maps__update____example2__iso__hyg29 a))
    (coqbool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_maps__U2_lf__U_maps__update____example2__iso__hyg31 a))
    (coqbool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_maps__U2_lf__U_maps__update____example2__iso__hyg33 a))
    (coqbool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_maps__U2_lf__U_maps__update____example2__iso__hyg35 a))
    (coqbool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_maps__U2_lf__U_maps__update____example2__iso__hyg37 a)).

Lemma ascii_roundtrip : forall a, IsomorphismDefinitions.eq (coqascii_to_ascii (ascii_to_coqascii a)) a.
Proof.
  intros [b0 b1 b2 b3 b4 b5 b6 b7].
  unfold ascii_to_coqascii, coqascii_to_ascii. simpl.
  destruct b0, b1, b2, b3, b4, b5, b6, b7; exact IsomorphismDefinitions.eq_refl.
Qed.

Lemma bool_coqbool_roundtrip : forall b, bool_to_coqbool (coqbool_to_bool b) = b.
Proof. destruct b; reflexivity. Qed.

Lemma coqascii_roundtrip : forall a, IsomorphismDefinitions.eq (ascii_to_coqascii (coqascii_to_ascii a)) a.
Proof.
  intros a. destruct a.
  unfold ascii_to_coqascii, coqascii_to_ascii. simpl.
  repeat rewrite bool_coqbool_roundtrip.
  apply IsomorphismDefinitions.eq_refl.
Qed.

Instance Ascii_ascii_iso : Iso Ascii.ascii imported_Ascii_ascii :=
  Build_Iso ascii_to_coqascii coqascii_to_ascii coqascii_roundtrip ascii_roundtrip.

Instance: KnownConstant Ascii.ascii := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Ascii_ascii := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Ascii.ascii Ascii_ascii_iso := {}.
Instance: IsoStatementProofBetween Ascii.ascii Imported.Ascii_ascii Ascii_ascii_iso := {}.