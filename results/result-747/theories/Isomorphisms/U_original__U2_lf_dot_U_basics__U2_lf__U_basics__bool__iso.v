From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_Original_LF__DOT__Basics_LF_Basics_bool : Type := Imported.Original_LF__DOT__Basics_LF_Basics_bool.

Definition bool_to_imported (x : Original.LF_DOT_Basics.LF.Basics.bool) : imported_Original_LF__DOT__Basics_LF_Basics_bool :=
  match x with
  | Original.LF_DOT_Basics.LF.Basics.true => Imported.Original_LF__DOT__Basics_LF_Basics_bool_true
  | Original.LF_DOT_Basics.LF.Basics.false => Imported.Original_LF__DOT__Basics_LF_Basics_bool_false
  end.

Definition bool_from_imported (y : imported_Original_LF__DOT__Basics_LF_Basics_bool) : Original.LF_DOT_Basics.LF.Basics.bool :=
  match y with
  | Imported.Original_LF__DOT__Basics_LF_Basics_bool_true => Original.LF_DOT_Basics.LF.Basics.true
  | Imported.Original_LF__DOT__Basics_LF_Basics_bool_false => Original.LF_DOT_Basics.LF.Basics.false
  end.

Lemma bool_to_from : forall x : imported_Original_LF__DOT__Basics_LF_Basics_bool,
  IsomorphismDefinitions.eq (bool_to_imported (bool_from_imported x)) x.
Proof.
  intro x. destruct x; apply IsomorphismDefinitions.eq_refl.
Qed.

Lemma bool_from_to : forall x : Original.LF_DOT_Basics.LF.Basics.bool,
  IsomorphismDefinitions.eq (bool_from_imported (bool_to_imported x)) x.
Proof.
  intro x. destruct x; apply IsomorphismDefinitions.eq_refl.
Qed.

Instance Original_LF__DOT__Basics_LF_Basics_bool_iso : Iso Original.LF_DOT_Basics.LF.Basics.bool imported_Original_LF__DOT__Basics_LF_Basics_bool :=
  Build_Iso bool_to_imported bool_from_imported bool_to_from bool_from_to.

Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.bool := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_bool := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.bool Original_LF__DOT__Basics_LF_Basics_bool_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.bool Imported.Original_LF__DOT__Basics_LF_Basics_bool Original_LF__DOT__Basics_LF_Basics_bool_iso := {}.