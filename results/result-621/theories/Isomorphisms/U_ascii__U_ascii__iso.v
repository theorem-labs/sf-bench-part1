From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_ascii__ascii__iso Isomorphisms.bool__iso.

Definition imported_Ascii_Ascii : imported_bool -> imported_bool -> imported_bool -> imported_bool -> imported_bool -> imported_bool -> imported_bool -> imported_bool -> imported_Ascii_ascii := Imported.ascii_Ascii.

Instance Ascii_Ascii_iso : forall (x1 : bool) (x2 : imported_bool),
  rel_iso bool_iso x1 x2 ->
  forall (x3 : bool) (x4 : imported_bool),
  rel_iso bool_iso x3 x4 ->
  forall (x5 : bool) (x6 : imported_bool),
  rel_iso bool_iso x5 x6 ->
  forall (x7 : bool) (x8 : imported_bool),
  rel_iso bool_iso x7 x8 ->
  forall (x9 : bool) (x10 : imported_bool),
  rel_iso bool_iso x9 x10 ->
  forall (x11 : bool) (x12 : imported_bool),
  rel_iso bool_iso x11 x12 ->
  forall (x13 : bool) (x14 : imported_bool),
  rel_iso bool_iso x13 x14 ->
  forall (x15 : bool) (x16 : imported_bool), rel_iso bool_iso x15 x16 -> rel_iso Ascii_ascii_iso (Ascii.Ascii x1 x3 x5 x7 x9 x11 x13 x15) (imported_Ascii_Ascii x2 x4 x6 x8 x10 x12 x14 x16).
Proof.
  intros x1 x2 H1 x3 x4 H3 x5 x6 H5 x7 x8 H7 x9 x10 H9 x11 x12 H11 x13 x14 H13 x15 x16 H15.
  unfold rel_iso. simpl.
  unfold ascii_to_imported, imported_Ascii_Ascii.
  unfold rel_iso in H1, H3, H5, H7, H9, H11, H13, H15.
  simpl in H1, H3, H5, H7, H9, H11, H13, H15.
  (* Each Hi : eq (bool_to_imported xi) x(i+1) *)
  apply (@IsoEq.eq_srect _ _ _ H1).
  apply (@IsoEq.eq_srect _ _ _ H3).
  apply (@IsoEq.eq_srect _ _ _ H5).
  apply (@IsoEq.eq_srect _ _ _ H7).
  apply (@IsoEq.eq_srect _ _ _ H9).
  apply (@IsoEq.eq_srect _ _ _ H11).
  apply (@IsoEq.eq_srect _ _ _ H13).
  apply (@IsoEq.eq_srect _ _ _ H15).
  exact IsomorphismDefinitions.eq_refl.
Qed.

Instance: KnownConstant Ascii.Ascii := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.ascii_Ascii := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Ascii.Ascii Ascii_Ascii_iso := {}.
Instance: IsoStatementProofBetween Ascii.Ascii Imported.ascii_Ascii Ascii_Ascii_iso := {}.
