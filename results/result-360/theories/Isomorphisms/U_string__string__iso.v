From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

(* Helper: bool <-> mybool isomorphism *)
Definition bool_to_mybool (b : bool) : Imported.mybool :=
  match b with
  | true => Imported.mybool_mytrue
  | false => Imported.mybool_myfalse
  end.

Definition mybool_to_bool (b : Imported.mybool) : bool :=
  match b with
  | Imported.mybool_mytrue => true
  | Imported.mybool_myfalse => false
  end.

(* Helper: Ascii.ascii <-> Imported.ascii isomorphism *)
Definition ascii_to_imported (a : Ascii.ascii) : Imported.ascii :=
  match a with
  | Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
      Imported.ascii_Ascii 
        (bool_to_mybool b0) (bool_to_mybool b1) 
        (bool_to_mybool b2) (bool_to_mybool b3)
        (bool_to_mybool b4) (bool_to_mybool b5) 
        (bool_to_mybool b6) (bool_to_mybool b7)
  end.

Definition imported_to_ascii (a : Imported.ascii) : Ascii.ascii :=
  Ascii.Ascii 
    (mybool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____informal____proof__iso__hyg28 a))
    (mybool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____informal____proof__iso__hyg30 a))
    (mybool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____informal____proof__iso__hyg32 a))
    (mybool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____informal____proof__iso__hyg34 a))
    (mybool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____informal____proof__iso__hyg36 a))
    (mybool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____informal____proof__iso__hyg38 a))
    (mybool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____informal____proof__iso__hyg40 a))
    (mybool_to_bool (Imported.a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____informal____proof__iso__hyg42 a)).

Definition imported_String_string : Type := Imported.String_string.
Instance String_string_iso : Iso String.string imported_String_string.
Proof.
  unshelve eapply Build_Iso.
  - (* to: String.string -> Imported.String_string *)
    fix to_string 1.
    intro s.
    destruct s as [|a s'].
    + exact Imported.String_string_EmptyString.
    + exact (Imported.String_string_String (ascii_to_imported a) (to_string s')).
  - (* from: Imported.String_string -> String.string *)
    fix from_string 1.
    intro s.
    destruct s as [|a s'].
    + exact String.EmptyString.
    + exact (String.String (imported_to_ascii a) (from_string s')).
  - (* to_from *)
    fix to_from 1.
    intro s.
    destruct s as [|a s'].
    + apply IsomorphismDefinitions.eq_refl.
    + simpl.
      assert (Ha : IsomorphismDefinitions.eq (ascii_to_imported (imported_to_ascii a)) a).
      { destruct a. simpl.
        destruct a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____informal____proof__iso__hyg28;
        destruct a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____informal____proof__iso__hyg30;
        destruct a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____informal____proof__iso__hyg32;
        destruct a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____informal____proof__iso__hyg34;
        destruct a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____informal____proof__iso__hyg36;
        destruct a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____informal____proof__iso__hyg38;
        destruct a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____informal____proof__iso__hyg40;
        destruct a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____informal____proof__iso__hyg42;
        apply IsomorphismDefinitions.eq_refl. }
      apply (IsoEq.f_equal2 Imported.String_string_String Ha (to_from s')).
  - (* from_to *)
    fix from_to 1.
    intro s.
    destruct s as [|a s'].
    + apply IsomorphismDefinitions.eq_refl.
    + simpl.
      assert (Ha : IsomorphismDefinitions.eq (imported_to_ascii (ascii_to_imported a)) a).
      { destruct a as [b0 b1 b2 b3 b4 b5 b6 b7]. simpl.
        destruct b0; destruct b1; destruct b2; destruct b3;
        destruct b4; destruct b5; destruct b6; destruct b7;
        apply IsomorphismDefinitions.eq_refl. }
      apply (IsoEq.f_equal2 String.String Ha (from_to s')).
Defined.
Instance: KnownConstant String.string := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.String_string := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor String.string String_string_iso := {}.
Instance: IsoStatementProofBetween String.string Imported.String_string String_string_iso := {}.