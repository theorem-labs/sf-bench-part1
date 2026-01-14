From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.

Definition imported_Ascii_ascii : Type := Imported.Ascii_ascii.

(* Convert from Stdlib bool to our bool *)
Definition stdlib_bool_to_LF (b : bool) : Original.LF_DOT_Basics.LF.Basics.bool :=
  match b with
  | true => Original.LF_DOT_Basics.LF.Basics.true
  | false => Original.LF_DOT_Basics.LF.Basics.false
  end.

Definition LF_bool_to_stdlib (b : Original.LF_DOT_Basics.LF.Basics.bool) : bool :=
  match b with
  | Original.LF_DOT_Basics.LF.Basics.true => true
  | Original.LF_DOT_Basics.LF.Basics.false => false
  end.

(* Build an isomorphism between Ascii.ascii (which uses Stdlib bool) and 
   Imported.Ascii_ascii (which uses Original_LF__DOT__Basics_LF_Basics_bool) *)
Definition ascii_to : Ascii.ascii -> imported_Ascii_ascii :=
  fun a => match a with
           | Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
             Imported.Ascii_ascii_Ascii
               (bool_to_imported (stdlib_bool_to_LF b0))
               (bool_to_imported (stdlib_bool_to_LF b1))
               (bool_to_imported (stdlib_bool_to_LF b2))
               (bool_to_imported (stdlib_bool_to_LF b3))
               (bool_to_imported (stdlib_bool_to_LF b4))
               (bool_to_imported (stdlib_bool_to_LF b5))
               (bool_to_imported (stdlib_bool_to_LF b6))
               (bool_to_imported (stdlib_bool_to_LF b7))
           end.

Definition ascii_from : imported_Ascii_ascii -> Ascii.ascii :=
  fun a => 
    Ascii.Ascii
      (LF_bool_to_stdlib (imported_to_bool (Imported.a____at___Solution__hyg68 a)))
      (LF_bool_to_stdlib (imported_to_bool (Imported.a____at___Solution__hyg70 a)))
      (LF_bool_to_stdlib (imported_to_bool (Imported.a____at___Solution__hyg72 a)))
      (LF_bool_to_stdlib (imported_to_bool (Imported.a____at___Solution__hyg74 a)))
      (LF_bool_to_stdlib (imported_to_bool (Imported.a____at___Solution__hyg76 a)))
      (LF_bool_to_stdlib (imported_to_bool (Imported.a____at___Solution__hyg78 a)))
      (LF_bool_to_stdlib (imported_to_bool (Imported.a____at___Solution__hyg80 a)))
      (LF_bool_to_stdlib (imported_to_bool (Imported.a____at___Solution__hyg82 a))).

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
  Imported.Ascii_ascii_indl
    (fun x => IsomorphismDefinitions.eq (ascii_to (ascii_from x)) x)
    ascii_to_from_aux.

Instance Ascii_ascii_iso : Iso Ascii.ascii imported_Ascii_ascii :=
  @Build_Iso Ascii.ascii imported_Ascii_ascii ascii_to ascii_from ascii_to_from ascii_from_to.

Instance: KnownConstant Ascii.ascii := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Ascii_ascii := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Ascii.ascii Ascii_ascii_iso := {}.
Instance: IsoStatementProofBetween Ascii.ascii Imported.Ascii_ascii Ascii_ascii_iso := {}.