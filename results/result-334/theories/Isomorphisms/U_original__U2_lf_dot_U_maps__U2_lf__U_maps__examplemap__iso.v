From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
From Stdlib Require Import String.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_string__string__iso Isomorphisms.bool__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____empty__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update__iso.

Definition imported_Original_LF__DOT__Maps_LF_Maps_examplemap : imported_String_string -> imported_bool := Imported.Original_LF__DOT__Maps_LF_Maps_examplemap.

(* Helper: convert from Coq bool to Imported.mybool *)
Definition bool_to_mybool' (b : bool) : Imported.mybool :=
  match b with
  | true => Imported.mybool_mytrue
  | false => Imported.mybool_myfalse
  end.

(* Define "foo" and "bar" in Coq's string representation *)
Local Open Scope string_scope.

(* Lemma: "foo" string converts correctly *)
Lemma foo_string_iso : rel_iso String_string_iso "foo" Imported.string_foo.
Proof.
  unfold rel_iso. simpl.
  unfold Imported.string_foo.
  unfold Imported.char_f, Imported.char_o.
  apply IsomorphismDefinitions.eq_refl.
Qed.

(* Lemma: "bar" string converts correctly *)
Lemma bar_string_iso : rel_iso String_string_iso "bar" Imported.string_bar.
Proof.
  unfold rel_iso. simpl.
  unfold Imported.string_bar.
  unfold Imported.char_b, Imported.char_a, Imported.char_r.
  apply IsomorphismDefinitions.eq_refl.
Qed.

Instance Original_LF__DOT__Maps_LF_Maps_examplemap_iso : forall (x1 : String.string) (x2 : imported_String_string),
  rel_iso String_string_iso x1 x2 -> rel_iso bool_iso (Original.LF_DOT_Maps.LF.Maps.examplemap x1) (imported_Original_LF__DOT__Maps_LF_Maps_examplemap x2).
Proof.
  intros x1 x2 Hx.
  (* Use the fact that examplemap is built from t_update and t_empty *)
  (* We can compose the isomorphisms *)
  unfold Original.LF_DOT_Maps.LF.Maps.examplemap, imported_Original_LF__DOT__Maps_LF_Maps_examplemap.
  unfold Imported.Original_LF__DOT__Maps_LF_Maps_examplemap.
  
  (* Helper: wrap rel_iso into rel_iso_sort for IsoIso *)
  assert (forall (a : bool) (b : Imported.mybool),
    rel_iso bool_iso a b -> @rel_iso_sort true bool Imported.mybool (IsoIso bool_iso) a b) as wrap_iso.
  { intros a b H. simpl. constructor. exact H. }
  
  (* Helper: unwrap rel_iso_sort for IsoIso back to rel_iso *)
  assert (forall (a : bool) (b : Imported.mybool),
    @rel_iso_sort true bool Imported.mybool (IsoIso bool_iso) a b -> rel_iso bool_iso a b) as unwrap_iso.
  { intros a b H. simpl in H. destruct H as [H']. exact H'. }
  
  (* Build up the proof step by step *)
  (* First, show the inner map (t_update (t_empty false) "foo" true) is isomorphic *)
  assert (forall (s1 : String.string) (s2 : imported_String_string),
    rel_iso String_string_iso s1 s2 ->
    @rel_iso_sort true bool Imported.mybool (IsoIso bool_iso)
      (Original.LF_DOT_Maps.LF.Maps.t_update (Original.LF_DOT_Maps.LF.Maps.t_empty false) "foo" true s1)
      (Imported.Original_LF__DOT__Maps_LF_Maps_t__update Imported.mybool
         (Imported.Original_LF__DOT__Maps_LF_Maps_t__empty Imported.mybool Imported.mybool_myfalse)
         Imported.string_foo Imported.mybool_mytrue s2)) as H_inner.
  {
    intros s1 s2 Hs.
    apply (@Original_LF__DOT__Maps_LF_Maps_t__update_iso bool Imported.mybool (IsoIso bool_iso)).
    - (* t_empty false is isomorphic *)
      intros s1' s2' Hs'.
      apply wrap_iso.
      apply Original_LF__DOT__Maps_LF_Maps_t__empty_iso.
      + unfold rel_iso. simpl. apply IsomorphismDefinitions.eq_refl.
      + exact Hs'.
    - (* "foo" is isomorphic to string_foo *)
      exact foo_string_iso.
    - (* true is isomorphic to mybool_mytrue *)
      apply wrap_iso. unfold rel_iso. simpl. apply IsomorphismDefinitions.eq_refl.
    - exact Hs.
  }
  
  (* Now apply t_update isomorphism for the outer layer *)
  pose proof (@Original_LF__DOT__Maps_LF_Maps_t__update_iso bool Imported.mybool (IsoIso bool_iso)
    (Original.LF_DOT_Maps.LF.Maps.t_update (Original.LF_DOT_Maps.LF.Maps.t_empty false) "foo" true)
    (Imported.Original_LF__DOT__Maps_LF_Maps_t__update Imported.mybool
       (Imported.Original_LF__DOT__Maps_LF_Maps_t__empty Imported.mybool Imported.mybool_myfalse)
       Imported.string_foo Imported.mybool_mytrue)
    H_inner
    "bar" Imported.string_bar bar_string_iso
    true Imported.mybool_mytrue) as Houter.
  assert (@rel_iso_sort true bool Imported.mybool (IsoIso bool_iso) true Imported.mybool_mytrue) as Htrue.
  { apply wrap_iso. unfold rel_iso. simpl. apply IsomorphismDefinitions.eq_refl. }
  specialize (Houter Htrue x1 x2 Hx).
  apply unwrap_iso.
  exact Houter.
Qed.
Instance: KnownConstant Original.LF_DOT_Maps.LF.Maps.examplemap := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Maps_LF_Maps_examplemap := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Maps.LF.Maps.examplemap Original_LF__DOT__Maps_LF_Maps_examplemap_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Maps.LF.Maps.examplemap Imported.Original_LF__DOT__Maps_LF_Maps_examplemap Original_LF__DOT__Maps_LF_Maps_examplemap_iso := {}.