From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_Original_LF__DOT__Basics_LF_Basics_bool : Type := Imported.Original_LF__DOT__Basics_LF_Basics_bool.

(* Forward: Original.bool -> Imported.bool *)
Definition bool_to_imported (b : Original.LF_DOT_Basics.LF.Basics.bool) : Imported.Original_LF__DOT__Basics_LF_Basics_bool :=
  match b with
  | Original.LF_DOT_Basics.LF.Basics.true => Imported.Original_LF__DOT__Basics_LF_Basics_bool_true
  | Original.LF_DOT_Basics.LF.Basics.false => Imported.Original_LF__DOT__Basics_LF_Basics_bool_false
  end.

(* Backward: Imported.bool -> Original.bool *)
Definition imported_to_bool (b : Imported.Original_LF__DOT__Basics_LF_Basics_bool) : Original.LF_DOT_Basics.LF.Basics.bool :=
  match b with
  | Imported.Original_LF__DOT__Basics_LF_Basics_bool_true => Original.LF_DOT_Basics.LF.Basics.true
  | Imported.Original_LF__DOT__Basics_LF_Basics_bool_false => Original.LF_DOT_Basics.LF.Basics.false
  end.

Lemma bool_roundtrip : forall b : Original.LF_DOT_Basics.LF.Basics.bool, 
  Logic.eq (imported_to_bool (bool_to_imported b)) b.
Proof.
  intros b. destruct b; reflexivity.
Qed.

Lemma imported_bool_roundtrip : forall b : Imported.Original_LF__DOT__Basics_LF_Basics_bool,
  Logic.eq (bool_to_imported (imported_to_bool b)) b.
Proof.
  intros b. destruct b; reflexivity.
Qed.

Instance Original_LF__DOT__Basics_LF_Basics_bool_iso : Iso Original.LF_DOT_Basics.LF.Basics.bool imported_Original_LF__DOT__Basics_LF_Basics_bool.
Proof.
  refine {|
    to := bool_to_imported;
    from := imported_to_bool;
    to_from := _;
    from_to := _
  |}.
  - intros b. apply seq_of_eq. apply imported_bool_roundtrip.
  - intros b. apply seq_of_eq. apply bool_roundtrip.
Defined.

Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.bool := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_bool := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.bool Original_LF__DOT__Basics_LF_Basics_bool_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.bool Imported.Original_LF__DOT__Basics_LF_Basics_bool Original_LF__DOT__Basics_LF_Basics_bool_iso := {}.