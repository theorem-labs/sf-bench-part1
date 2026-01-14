From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_andb : imported_Original_LF__DOT__Basics_LF_Basics_bool -> imported_Original_LF__DOT__Basics_LF_Basics_bool -> imported_Original_LF__DOT__Basics_LF_Basics_bool := Imported.Original_LF__DOT__Basics_LF_Basics_andb.
Instance Original_LF__DOT__Basics_LF_Basics_andb_iso : forall (x1 : Original.LF_DOT_Basics.LF.Basics.bool) (x2 : imported_Original_LF__DOT__Basics_LF_Basics_bool),
  rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso x1 x2 ->
  forall (x3 : Original.LF_DOT_Basics.LF.Basics.bool) (x4 : imported_Original_LF__DOT__Basics_LF_Basics_bool),
  rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso x3 x4 ->
  rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso (Original.LF_DOT_Basics.LF.Basics.andb x1 x3) (imported_Original_LF__DOT__Basics_LF_Basics_andb x2 x4).
Proof.
  intros x1 x2 H1 x3 x4 H2.
  unfold rel_iso in *.
  unfold imported_Original_LF__DOT__Basics_LF_Basics_andb.
  (* H1 : bool_to_imported x1 = x2 *)
  (* H2 : bool_to_imported x3 = x4 *)
  (* Goal: bool_to_imported (andb x1 x3) = Imported.andb x2 x4 *)
  destruct H1.
  destruct H2.
  (* Now x2 = bool_to_imported x1, x4 = bool_to_imported x3 *)
  (* Goal: bool_to_imported (andb x1 x3) = Imported.andb (bool_to_imported x1) (bool_to_imported x3) *)
  destruct x1, x3; simpl; apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.andb := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_andb := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.andb Original_LF__DOT__Basics_LF_Basics_andb_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.andb Imported.Original_LF__DOT__Basics_LF_Basics_andb Original_LF__DOT__Basics_LF_Basics_andb_iso := {}.