From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
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
  intros x1 x2 H12 x3 x4 H34.
  unfold rel_iso in *.
  unfold imported_Original_LF__DOT__Basics_LF_Basics_andb.
  simpl in *.
  (* H12: to(bool_iso) x1 = x2, H34: to(bool_iso) x3 = x4 *)
  (* Goal: to(bool_iso) (andb x1 x3) = andb x2 x4 *)
  destruct x1; simpl.
  - (* x1 = true: andb true x3 = x3, andb x2 x4 = ? *)
    (* We need to show: to x3 = andb (to true) x4 *)
    (* Since H12 says to true = x2, i.e., x2 = true_imported *)
    (* And imported andb true_imported x4 = x4 *)
    (* So we need to show: to x3 = x4, which is H34 *)
    assert (Hx2 : x2 = Imported.Original_LF__DOT__Basics_LF_Basics_bool_Original_LF__DOT__Basics_LF_Basics_bool_true).
    { symmetry. apply (IsoEq.eq_of_seq H12). }
    rewrite Hx2.
    simpl.
    exact H34.
  - (* x1 = false: andb false x3 = false *)
    (* We need to show: to false = andb x2 x4 *)
    (* H12 says: to false = x2, i.e., x2 = false_imported *)
    (* imported andb false_imported x4 = false_imported *)
    assert (Hx2 : x2 = Imported.Original_LF__DOT__Basics_LF_Basics_bool_Original_LF__DOT__Basics_LF_Basics_bool_false).
    { symmetry. apply (IsoEq.eq_of_seq H12). }
    rewrite Hx2.
    simpl.
    apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.andb := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_andb := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.andb Original_LF__DOT__Basics_LF_Basics_andb_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.andb Imported.Original_LF__DOT__Basics_LF_Basics_andb Original_LF__DOT__Basics_LF_Basics_andb_iso := {}.