From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
From Stdlib Require Import String.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_string__string__iso Isomorphisms.bool__iso Isomorphisms.option__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__update__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__empty__iso.

Definition imported_Original_LF__DOT__Maps_LF_Maps_examplepmap : imported_String_string -> imported_option imported_bool := Imported.Original_LF__DOT__Maps_LF_Maps_examplepmap.

(* examplepmap = update (update empty "Turing" false) "Church" true *)
(* We need to prove that the two sides are related *)

(* First, prove the strings are related *)
Local Open Scope string_scope.

Lemma Church_string_iso : rel_iso String_string_iso "Church" Imported.string_Church.
Proof.
  unfold rel_iso. simpl.
  (* string_to_imported "Church" = string_Church *)
  unfold string_to_imported, ascii_to_imported, bool_to_Bool.
  reflexivity.
Qed.

Lemma Turing_string_iso : rel_iso String_string_iso "Turing" Imported.string_Turing.
Proof.
  unfold rel_iso. simpl.
  unfold string_to_imported, ascii_to_imported, bool_to_Bool.
  reflexivity.
Qed.

Lemma true_bool_iso : rel_iso bool_iso true Imported.Rocq_Bool_true.
Proof.
  unfold rel_iso. simpl.
  unfold bool_to_imported.
  reflexivity.
Qed.

Lemma false_bool_iso : rel_iso bool_iso false Imported.Rocq_Bool_false.
Proof.
  unfold rel_iso. simpl.
  unfold bool_to_imported.
  reflexivity.
Qed.

Instance Original_LF__DOT__Maps_LF_Maps_examplepmap_iso : forall (x1 : String.string) (x2 : imported_String_string),
  rel_iso String_string_iso x1 x2 -> rel_iso (option_iso bool_iso) (Original.LF_DOT_Maps.LF.Maps.examplepmap x1) (imported_Original_LF__DOT__Maps_LF_Maps_examplepmap x2).
Proof.
  intros x1 x2 Hx.
  unfold Original.LF_DOT_Maps.LF.Maps.examplepmap.
  unfold imported_Original_LF__DOT__Maps_LF_Maps_examplepmap.
  unfold Imported.Original_LF__DOT__Maps_LF_Maps_examplepmap.
  (* examplepmap = update (update empty "Turing" false) "Church" true *)
  (* We need to apply the update_iso lemma twice *)
  
  (* First expand the Coq side *)
  (* ("Church" |-> true ; "Turing" |-> false) = update (update empty "Turing" false) "Church" true *)
  
  apply Original_LF__DOT__Maps_LF_Maps_update_iso.
  - (* The inner map (update empty "Turing" false) is isomorphic *)
    intros s1 s2 Hs.
    apply Original_LF__DOT__Maps_LF_Maps_update_iso.
    + (* empty is isomorphic *)
      intros s1' s2' Hs'.
      apply Original_LF__DOT__Maps_LF_Maps_empty_iso.
      exact Hs'.
    + (* "Turing" is related *)
      exact Turing_string_iso.
    + (* false is related *)
      exact false_bool_iso.
    + exact Hs.
  - (* "Church" is related *)
    exact Church_string_iso.
  - (* true is related *)
    exact true_bool_iso.
  - (* x1 x2 are related *)
    exact Hx.
Qed.

Instance: KnownConstant Original.LF_DOT_Maps.LF.Maps.examplepmap := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Maps_LF_Maps_examplepmap := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Maps.LF.Maps.examplepmap Original_LF__DOT__Maps_LF_Maps_examplepmap_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Maps.LF.Maps.examplepmap Imported.Original_LF__DOT__Maps_LF_Maps_examplepmap Original_LF__DOT__Maps_LF_Maps_examplepmap_iso := {}.
