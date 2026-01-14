From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

(* Bool isomorphism *)
Definition mybool_to (b : Datatypes.bool) : Imported.Datatypes_bool :=
  match b with
  | Datatypes.true => Imported.Datatypes_bool_true
  | Datatypes.false => Imported.Datatypes_bool_false
  end.

Definition mybool_from (b : Imported.Datatypes_bool) : Datatypes.bool :=
  match b with
  | Imported.Datatypes_bool_true => Datatypes.true
  | Imported.Datatypes_bool_false => Datatypes.false
  end.

Lemma mybool_to_from : forall b, IsomorphismDefinitions.eq (mybool_to (mybool_from b)) b.
Proof.
  intros []; apply IsomorphismDefinitions.eq_refl.
Defined.

Lemma mybool_from_to : forall b, IsomorphismDefinitions.eq (mybool_from (mybool_to b)) b.
Proof.
  intros []; apply IsomorphismDefinitions.eq_refl.
Defined.

Definition mybool_iso : Iso Datatypes.bool Imported.Datatypes_bool :=
  Build_Iso mybool_to mybool_from mybool_to_from mybool_from_to.

Definition imported_Ascii_ascii : Type := Imported.Ascii_ascii.

Definition ascii_to (a : Ascii.ascii) : Imported.Ascii_ascii :=
  match a with
  | Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    Imported.Ascii_ascii_Ascii (mybool_to b0) (mybool_to b1) (mybool_to b2) (mybool_to b3)
                               (mybool_to b4) (mybool_to b5) (mybool_to b6) (mybool_to b7)
  end.

(* Shorter names for projections *)
Local Notation proj0 := Imported.a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____fold____map__iso__hyg35.
Local Notation proj1 := Imported.a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____fold____map__iso__hyg37.
Local Notation proj2 := Imported.a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____fold____map__iso__hyg39.
Local Notation proj3 := Imported.a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____fold____map__iso__hyg41.
Local Notation proj4 := Imported.a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____fold____map__iso__hyg43.
Local Notation proj5 := Imported.a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____fold____map__iso__hyg45.
Local Notation proj6 := Imported.a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____fold____map__iso__hyg47.
Local Notation proj7 := Imported.a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____fold____map__iso__hyg49.

Definition ascii_from (a : Imported.Ascii_ascii) : Ascii.ascii :=
  Ascii.Ascii (mybool_from (proj0 a)) (mybool_from (proj1 a)) 
              (mybool_from (proj2 a)) (mybool_from (proj3 a))
              (mybool_from (proj4 a)) (mybool_from (proj5 a)) 
              (mybool_from (proj6 a)) (mybool_from (proj7 a)).

Lemma ascii_to_from : forall a, IsomorphismDefinitions.eq (ascii_to (ascii_from a)) a.
Proof.
  intro a.
  destruct a.
  simpl.
  destruct a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____fold____map__iso__hyg35,
           a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____fold____map__iso__hyg37,
           a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____fold____map__iso__hyg39,
           a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____fold____map__iso__hyg41,
           a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____fold____map__iso__hyg43,
           a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____fold____map__iso__hyg45,
           a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____fold____map__iso__hyg47,
           a____at___U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__manual____grade____for____fold____map__iso__hyg49.
  all: simpl; apply IsomorphismDefinitions.eq_refl.
Defined.

Lemma ascii_from_to : forall a, IsomorphismDefinitions.eq (ascii_from (ascii_to a)) a.
Proof.
  intros [b0 b1 b2 b3 b4 b5 b6 b7]. simpl.
  destruct b0, b1, b2, b3, b4, b5, b6, b7.
  all: simpl; apply IsomorphismDefinitions.eq_refl.
Defined.

Instance Ascii_ascii_iso : Iso Ascii.ascii imported_Ascii_ascii :=
  Build_Iso ascii_to ascii_from ascii_to_from ascii_from_to.

Instance: KnownConstant Ascii.ascii := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Ascii_ascii := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Ascii.ascii Ascii_ascii_iso := {}.
Instance: IsoStatementProofBetween Ascii.ascii Imported.Ascii_ascii Ascii_ascii_iso := {}.