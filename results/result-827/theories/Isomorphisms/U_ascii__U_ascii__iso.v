From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_ascii__ascii__iso Isomorphisms.bool__iso.

Definition imported_Ascii_Ascii : imported_bool -> imported_bool -> imported_bool -> imported_bool -> imported_bool -> imported_bool -> imported_bool -> imported_bool -> imported_Ascii_ascii := Imported.Ascii_Ascii.

(* Define f_equal8 in terms of existing f_equal lemmas *)
Lemma f_equal8 {A1 A2 A3 A4 A5 A6 A7 A8 B : Type}
  (f : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> B)
  {x1 y1 : A1} {x2 y2 : A2} {x3 y3 : A3} {x4 y4 : A4}
  {x5 y5 : A5} {x6 y6 : A6} {x7 y7 : A7} {x8 y8 : A8} :
  IsomorphismDefinitions.eq x1 y1 ->
  IsomorphismDefinitions.eq x2 y2 ->
  IsomorphismDefinitions.eq x3 y3 ->
  IsomorphismDefinitions.eq x4 y4 ->
  IsomorphismDefinitions.eq x5 y5 ->
  IsomorphismDefinitions.eq x6 y6 ->
  IsomorphismDefinitions.eq x7 y7 ->
  IsomorphismDefinitions.eq x8 y8 ->
  IsomorphismDefinitions.eq (f x1 x2 x3 x4 x5 x6 x7 x8) (f y1 y2 y3 y4 y5 y6 y7 y8).
Proof.
  intros h1 h2 h3 h4 h5 h6 h7 h8.
  destruct h1, h2, h3, h4, h5, h6, h7, h8.
  exact IsomorphismDefinitions.eq_refl.
Defined.

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
  intros x1 x2 h1 x3 x4 h3 x5 x6 h5 x7 x8 h7 x9 x10 h9 x11 x12 h11 x13 x14 h13 x15 x16 h15.
  unfold rel_iso in *. simpl in *.
  unfold imported_Ascii_Ascii, ascii_to_imported, bool_to_mybool.
  apply f_equal8; assumption.
Defined.

Instance: KnownConstant Ascii.Ascii := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Ascii_Ascii := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Ascii.Ascii Ascii_Ascii_iso := {}.
Instance: IsoStatementProofBetween Ascii.Ascii Imported.Ascii_Ascii Ascii_Ascii_iso := {}.