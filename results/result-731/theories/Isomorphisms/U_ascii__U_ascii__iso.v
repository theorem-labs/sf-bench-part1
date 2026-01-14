From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_ascii__ascii__iso Isomorphisms.bool__iso.

Definition imported_Ascii_Ascii : imported_bool -> imported_bool -> imported_bool -> imported_bool -> imported_bool -> imported_bool -> imported_bool -> imported_bool -> imported_Ascii_ascii := Imported.Ascii_ascii_Ascii.
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
  intros x1 x2 H12 x3 x4 H34 x5 x6 H56 x7 x8 H78 x9 x10 H910 x11 x12 H1112 x13 x14 H1314 x15 x16 H1516.
  unfold rel_iso in *. simpl in *.
  unfold imported_Ascii_Ascii.
  (* Note: to bool_iso = (fun b => if b then mytrue else myfalse) *)
  (* and ascii_to = (fun a => match a with Ascii ... => Ascii_ascii_Ascii (bool_to_mybool ...) ... end) *)
  (* where bool_to_mybool = to bool_iso *)
  (* So to Ascii_ascii_iso (Ascii.Ascii x1..x15) = Ascii_ascii_Ascii (to bool_iso x1) ... (to bool_iso x15) *)
  (* We need to show this equals Ascii_ascii_Ascii x2 x4 ... x16 *)
  (* Using that H12 : to bool_iso x1 = x2, etc *)
  
  (* Chain of f_equal applications *)
  pose proof (f_equal (fun b => Imported.Ascii_ascii_Ascii b (to bool_iso x3) (to bool_iso x5) (to bool_iso x7) (to bool_iso x9) (to bool_iso x11) (to bool_iso x13) (to bool_iso x15)) H12) as step1.
  pose proof (f_equal (fun b => Imported.Ascii_ascii_Ascii x2 b (to bool_iso x5) (to bool_iso x7) (to bool_iso x9) (to bool_iso x11) (to bool_iso x13) (to bool_iso x15)) H34) as step2.
  pose proof (f_equal (fun b => Imported.Ascii_ascii_Ascii x2 x4 b (to bool_iso x7) (to bool_iso x9) (to bool_iso x11) (to bool_iso x13) (to bool_iso x15)) H56) as step3.
  pose proof (f_equal (fun b => Imported.Ascii_ascii_Ascii x2 x4 x6 b (to bool_iso x9) (to bool_iso x11) (to bool_iso x13) (to bool_iso x15)) H78) as step4.
  pose proof (f_equal (fun b => Imported.Ascii_ascii_Ascii x2 x4 x6 x8 b (to bool_iso x11) (to bool_iso x13) (to bool_iso x15)) H910) as step5.
  pose proof (f_equal (fun b => Imported.Ascii_ascii_Ascii x2 x4 x6 x8 x10 b (to bool_iso x13) (to bool_iso x15)) H1112) as step6.
  pose proof (f_equal (fun b => Imported.Ascii_ascii_Ascii x2 x4 x6 x8 x10 x12 b (to bool_iso x15)) H1314) as step7.
  pose proof (f_equal (fun b => Imported.Ascii_ascii_Ascii x2 x4 x6 x8 x10 x12 x14 b) H1516) as step8.
  
  apply (eq_trans step1).
  apply (eq_trans step2).
  apply (eq_trans step3).
  apply (eq_trans step4).
  apply (eq_trans step5).
  apply (eq_trans step6).
  apply (eq_trans step7).
  exact step8.
Defined.
Instance: KnownConstant Ascii.Ascii := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Ascii_ascii_Ascii := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Ascii.Ascii Ascii_Ascii_iso := {}.
Instance: IsoStatementProofBetween Ascii.Ascii Imported.Ascii_ascii_Ascii Ascii_Ascii_iso := {}.