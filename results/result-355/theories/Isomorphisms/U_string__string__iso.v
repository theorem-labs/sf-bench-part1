From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

(* First we need isomorphisms for bool and ascii *)
Definition bool_to : bool -> Imported.mybool :=
  fun b => match b with
           | true => Imported.mybool_true
           | false => Imported.mybool_false
           end.

Definition bool_from : Imported.mybool -> bool :=
  fun b => match b with
           | Imported.mybool_true => true
           | Imported.mybool_false => false
           end.

Definition ascii_to : Ascii.ascii -> Imported.ascii :=
  fun a => match a with
           | Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
             Imported.ascii_Ascii (bool_to b0) (bool_to b1) (bool_to b2) (bool_to b3)
                                  (bool_to b4) (bool_to b5) (bool_to b6) (bool_to b7)
           end.

Definition ascii_from : Imported.ascii -> Ascii.ascii :=
  fun a => Ascii.Ascii
             (bool_from (Imported.a____at___U_original__U2_lf_dot_U_logic__U2_lf__U_logic__manual____grade____for____double____neg____informal__iso__hyg28 a))
             (bool_from (Imported.a____at___U_original__U2_lf_dot_U_logic__U2_lf__U_logic__manual____grade____for____double____neg____informal__iso__hyg30 a))
             (bool_from (Imported.a____at___U_original__U2_lf_dot_U_logic__U2_lf__U_logic__manual____grade____for____double____neg____informal__iso__hyg32 a))
             (bool_from (Imported.a____at___U_original__U2_lf_dot_U_logic__U2_lf__U_logic__manual____grade____for____double____neg____informal__iso__hyg34 a))
             (bool_from (Imported.a____at___U_original__U2_lf_dot_U_logic__U2_lf__U_logic__manual____grade____for____double____neg____informal__iso__hyg36 a))
             (bool_from (Imported.a____at___U_original__U2_lf_dot_U_logic__U2_lf__U_logic__manual____grade____for____double____neg____informal__iso__hyg38 a))
             (bool_from (Imported.a____at___U_original__U2_lf_dot_U_logic__U2_lf__U_logic__manual____grade____for____double____neg____informal__iso__hyg40 a))
             (bool_from (Imported.a____at___U_original__U2_lf_dot_U_logic__U2_lf__U_logic__manual____grade____for____double____neg____informal__iso__hyg42 a)).

Definition imported_String_string : Type := Imported.String_string.

Instance String_string_iso : Iso String.string imported_String_string.
Proof.
  unshelve eapply Build_Iso.
  - (* to: String.string -> Imported.String_string *)
    fix str_to 1.
    intro s.
    destruct s as [|c s'].
    + exact Imported.String_string_EmptyString.
    + exact (Imported.String_string_String (ascii_to c) (str_to s')).
  - (* from: Imported.String_string -> String.string *)
    fix str_from 1.
    intro s.
    destruct s as [|c s'].
    + exact String.EmptyString.
    + exact (String.String (ascii_from c) (str_from s')).
  - (* to_from *)
    fix to_from 1.
    intro s.
    destruct s as [|c s'].
    + apply IsomorphismDefinitions.eq_refl.
    + simpl.
      apply (IsoEq.f_equal2 Imported.String_string_String).
      * (* ascii_to (ascii_from c) = c *)
        destruct c.
        unfold ascii_from, ascii_to. simpl.
        destruct a____at___U_original__U2_lf_dot_U_logic__U2_lf__U_logic__manual____grade____for____double____neg____informal__iso__hyg28;
        destruct a____at___U_original__U2_lf_dot_U_logic__U2_lf__U_logic__manual____grade____for____double____neg____informal__iso__hyg30;
        destruct a____at___U_original__U2_lf_dot_U_logic__U2_lf__U_logic__manual____grade____for____double____neg____informal__iso__hyg32;
        destruct a____at___U_original__U2_lf_dot_U_logic__U2_lf__U_logic__manual____grade____for____double____neg____informal__iso__hyg34;
        destruct a____at___U_original__U2_lf_dot_U_logic__U2_lf__U_logic__manual____grade____for____double____neg____informal__iso__hyg36;
        destruct a____at___U_original__U2_lf_dot_U_logic__U2_lf__U_logic__manual____grade____for____double____neg____informal__iso__hyg38;
        destruct a____at___U_original__U2_lf_dot_U_logic__U2_lf__U_logic__manual____grade____for____double____neg____informal__iso__hyg40;
        destruct a____at___U_original__U2_lf_dot_U_logic__U2_lf__U_logic__manual____grade____for____double____neg____informal__iso__hyg42;
        apply IsomorphismDefinitions.eq_refl.
      * apply (to_from s').
  - (* from_to *)
    fix from_to 1.
    intro s.
    destruct s as [|c s'].
    + apply IsomorphismDefinitions.eq_refl.
    + simpl.
      apply (IsoEq.f_equal2 String.String).
      * (* ascii_from (ascii_to c) = c *)
        destruct c as [b0 b1 b2 b3 b4 b5 b6 b7].
        unfold ascii_from, ascii_to. simpl.
        destruct b0; destruct b1; destruct b2; destruct b3;
        destruct b4; destruct b5; destruct b6; destruct b7;
        apply IsomorphismDefinitions.eq_refl.
      * apply (from_to s').
Defined.

Instance: KnownConstant String.string := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.String_string := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor String.string String_string_iso := {}.
Instance: IsoStatementProofBetween String.string Imported.String_string String_string_iso := {}.