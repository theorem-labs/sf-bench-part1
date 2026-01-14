From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.
From IsomorphismChecker Require Export Isomorphisms.bool__iso.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

Definition imported_Original_LF__DOT__Maps_LF_Maps_t__update : forall x : Type, (imported_String_string -> x) -> imported_String_string -> x -> imported_String_string -> x := (@Imported.Original_LF__DOT__Maps_LF_Maps_t__update).

(* Show that string equality is preserved under the isomorphism *)
Lemma string_eqb_compat : forall s1 s2 : String.string,
  bool_to_coqbool (String.eqb s1 s2) = Imported.Coqstring_eqb (string_to_coqstring s1) (string_to_coqstring s2).
Proof.
  intro s1. induction s1 as [| c1 rest1 IH]; intros [| c2 rest2].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl.
    (* Check if c1 = c2 using ascii equality *)
    destruct c1 as [b0 b1 b2 b3 b4 b5 b6 b7].
    destruct c2 as [d0 d1 d2 d3 d4 d5 d6 d7].
    simpl.
    destruct b0, b1, b2, b3, b4, b5, b6, b7, d0, d1, d2, d3, d4, d5, d6, d7;
    simpl; try reflexivity; try apply IH.
Qed.

(* Prove that Coqstring_eqb gives Coqbool_true iff String.eqb gives true *)
Lemma string_eqb_true_iff : forall s1 s2 : String.string,
  String.eqb s1 s2 = true <-> Imported.Coqstring_eqb (string_to_coqstring s1) (string_to_coqstring s2) = Imported.Coqbool_true.
Proof.
  intros s1 s2.
  rewrite <- string_eqb_compat.
  destruct (String.eqb s1 s2); split; intro H; try reflexivity; try discriminate.
Qed.

Lemma string_eqb_false_iff : forall s1 s2 : String.string,
  String.eqb s1 s2 = false <-> Imported.Coqstring_eqb (string_to_coqstring s1) (string_to_coqstring s2) = Imported.Coqbool_false.
Proof.
  intros s1 s2.
  rewrite <- string_eqb_compat.
  destruct (String.eqb s1 s2); split; intro H; try reflexivity; try discriminate.
Qed.

(* The key lemma about the imported match function *)
Lemma imported_match_true : forall (A : Type) (v1 v2 : Imported.Unit -> A),
  Imported.Original_LF__DOT__Maps_LF_Maps_t__update_match_1 (fun _ => A) Imported.Coqbool_true v1 v2 = v1 Imported.Unit_unit.
Proof. reflexivity. Qed.

Lemma imported_match_false : forall (A : Type) (v1 v2 : Imported.Unit -> A),
  Imported.Original_LF__DOT__Maps_LF_Maps_t__update_match_1 (fun _ => A) Imported.Coqbool_false v1 v2 = v2 Imported.Unit_unit.
Proof. reflexivity. Qed.

Instance Original_LF__DOT__Maps_LF_Maps_t__update_iso : forall (x1 x2 : Type) (hx : IsoOrSortRelaxed x1 x2) (x3 : Original.LF_DOT_Maps.LF.Maps.total_map x1) (x4 : imported_String_string -> x2),
  (forall (x5 : String.string) (x6 : imported_String_string), rel_iso String_string_iso x5 x6 -> rel_iso_sort hx (x3 x5) (x4 x6)) ->
  forall (x5 : String.string) (x6 : imported_String_string),
  rel_iso String_string_iso x5 x6 ->
  forall (x7 : x1) (x8 : x2),
  rel_iso_sort hx x7 x8 ->
  forall (x9 : String.string) (x10 : imported_String_string),
  rel_iso String_string_iso x9 x10 -> rel_iso_sort hx (Original.LF_DOT_Maps.LF.Maps.t_update x3 x5 x7 x9) (imported_Original_LF__DOT__Maps_LF_Maps_t__update x4 x6 x8 x10).
Proof.
  intros x1 x2 hx m1 m2 Hm key1 key2 Hkey val1 val2 Hval query1 query2 Hquery.
  unfold Original.LF_DOT_Maps.LF.Maps.t_update.
  unfold imported_Original_LF__DOT__Maps_LF_Maps_t__update.
  unfold Imported.Original_LF__DOT__Maps_LF_Maps_t__update.
  (* rel_iso String_string_iso s1 s2 means to(s1) = s2 in SProp *)
  (* Use eq_of_seq to convert SProp eq to Type eq *)
  assert (Hkey2 : key2 = string_to_coqstring key1).
  { unfold rel_iso in Hkey. simpl in Hkey.
    symmetry. apply eq_of_seq. exact Hkey. }
  assert (Hquery2 : query2 = string_to_coqstring query1).
  { unfold rel_iso in Hquery. simpl in Hquery.
    symmetry. apply eq_of_seq. exact Hquery. }
  rewrite Hkey2, Hquery2.
  rewrite <- string_eqb_compat.
  destruct (String.eqb key1 query1) eqn:Heqb; simpl.
  - (* keys equal - return val *)
    exact Hval.
  - (* keys different - return m query *)
    apply Hm.
    unfold rel_iso. simpl.
    apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant (@Original.LF_DOT_Maps.LF.Maps.t_update) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Original_LF__DOT__Maps_LF_Maps_t__update) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF_DOT_Maps.LF.Maps.t_update) Original_LF__DOT__Maps_LF_Maps_t__update_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_Maps.LF.Maps.t_update) (@Imported.Original_LF__DOT__Maps_LF_Maps_t__update) Original_LF__DOT__Maps_LF_Maps_t__update_iso := {}.