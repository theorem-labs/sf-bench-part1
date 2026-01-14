From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

From IsomorphismChecker Require Export Isomorphisms.bool__iso.

(* The Imported module has Ascii_ascii with 8 Bool fields *)
Definition imported_Ascii_ascii : Type := Imported.Ascii_ascii.

(* Build an isomorphism between Ascii.ascii (which uses Stdlib bool) and 
   Imported.Ascii_ascii (which uses Imported.Bool) *)
Definition ascii_to : Ascii.ascii -> imported_Ascii_ascii :=
  fun a => match a with
           | Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
             Imported.Ascii_ascii_Ascii
               (bool_to b0) (bool_to b1) (bool_to b2) (bool_to b3)
               (bool_to b4) (bool_to b5) (bool_to b6) (bool_to b7)
           end.

Definition ascii_from : imported_Ascii_ascii -> Ascii.ascii :=
  fun a => 
    Ascii.Ascii
      (bool_from (Imported.a____at___U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__test____der0__iso__hyg26 a))
      (bool_from (Imported.a____at___U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__test____der0__iso__hyg28 a))
      (bool_from (Imported.a____at___U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__test____der0__iso__hyg30 a))
      (bool_from (Imported.a____at___U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__test____der0__iso__hyg32 a))
      (bool_from (Imported.a____at___U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__test____der0__iso__hyg34 a))
      (bool_from (Imported.a____at___U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__test____der0__iso__hyg36 a))
      (bool_from (Imported.a____at___U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__test____der0__iso__hyg38 a))
      (bool_from (Imported.a____at___U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__test____der0__iso__hyg40 a)).

(* from_to: for x : Ascii.ascii, ascii_from (ascii_to x) = x *)
Lemma ascii_from_to_aux : forall b0 b1 b2 b3 b4 b5 b6 b7,
  IsomorphismDefinitions.eq 
    (ascii_from (ascii_to (Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7))) 
    (Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7).
Proof.
  intros b0 b1 b2 b3 b4 b5 b6 b7.
  destruct b0, b1, b2, b3, b4, b5, b6, b7; exact IsomorphismDefinitions.eq_refl.
Defined.

Definition ascii_from_to : forall x, IsomorphismDefinitions.eq (ascii_from (ascii_to x)) x :=
  fun x => match x with
           | Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7 => ascii_from_to_aux b0 b1 b2 b3 b4 b5 b6 b7
           end.

(* to_from: for x : imported_Ascii_ascii, ascii_to (ascii_from x) = x *)
Lemma ascii_to_from_aux : forall b0 b1 b2 b3 b4 b5 b6 b7,
  IsomorphismDefinitions.eq 
    (ascii_to (ascii_from (Imported.Ascii_ascii_Ascii b0 b1 b2 b3 b4 b5 b6 b7)))
    (Imported.Ascii_ascii_Ascii b0 b1 b2 b3 b4 b5 b6 b7).
Proof.
  intros b0 b1 b2 b3 b4 b5 b6 b7.
  destruct b0, b1, b2, b3, b4, b5, b6, b7; exact IsomorphismDefinitions.eq_refl.
Defined.

Definition ascii_to_from : forall x, IsomorphismDefinitions.eq (ascii_to (ascii_from x)) x :=
  fun x => match x with
           | Imported.Ascii_ascii_Ascii b0 b1 b2 b3 b4 b5 b6 b7 => ascii_to_from_aux b0 b1 b2 b3 b4 b5 b6 b7
           end.

Instance Ascii_ascii_iso : Iso Ascii.ascii imported_Ascii_ascii :=
  @Build_Iso Ascii.ascii imported_Ascii_ascii ascii_to ascii_from ascii_to_from ascii_from_to.

Instance: KnownConstant Ascii.ascii := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Ascii_ascii := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Ascii.ascii Ascii_ascii_iso := {}.
Instance: IsoStatementProofBetween Ascii.ascii Imported.Ascii_ascii Ascii_ascii_iso := {}.