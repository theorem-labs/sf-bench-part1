From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
(* Typeclasses Opaque rel_iso. *) (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__partial____map__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update__iso.

Definition imported_Original_LF__DOT__Maps_LF_Maps_update : forall x : Type, (imported_String_string -> imported_option x) -> imported_String_string -> x -> imported_String_string -> imported_option x := (@Imported.Original_LF__DOT__Maps_LF_Maps_update).

(* Helper: convert between Coq bool and Imported.mybool *)
Definition bool_to_mybool' (b : bool) : Imported.mybool :=
  match b with
  | true => Imported.mybool_mytrue
  | false => Imported.mybool_myfalse
  end.

Instance Original_LF__DOT__Maps_LF_Maps_update_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_Maps.LF.Maps.partial_map x1) (x4 : imported_String_string -> imported_option x2),
  (forall (x5 : String.string) (x6 : imported_String_string), rel_iso String_string_iso x5 x6 -> rel_iso (option_iso hx) (x3 x5) (x4 x6)) ->
  forall (x5 : String.string) (x6 : imported_String_string),
  rel_iso String_string_iso x5 x6 ->
  forall (x7 : x1) (x8 : x2),
  rel_iso hx x7 x8 ->
  forall (x9 : String.string) (x10 : imported_String_string),
  rel_iso String_string_iso x9 x10 -> rel_iso (option_iso hx) (Original.LF_DOT_Maps.LF.Maps.update x3 x5 x7 x9) (imported_Original_LF__DOT__Maps_LF_Maps_update x4 x6 x8 x10).
Proof.
  intros x1 x2 hx x3 x4 Hmap x5 x6 H56 x7 x8 H78 x9 x10 H910.
  unfold Original.LF_DOT_Maps.LF.Maps.update.
  unfold imported_Original_LF__DOT__Maps_LF_Maps_update, Imported.Original_LF__DOT__Maps_LF_Maps_update.
  unfold Original.LF_DOT_Maps.LF.Maps.t_update, Imported.Original_LF__DOT__Maps_LF_Maps_t__update.
  pose proof (@string_eqb_compat x5 x9 x6 x10 H56 H910) as Heqb.
  destruct (String.eqb x5 x9) eqn:E1.
  - (* k1 = x1' in Coq, so String_eqb k2 x2' should be mybool_mytrue *)
    assert (Imported.String_eqb x6 x10 = Imported.mybool_mytrue) as E2.
    { apply eq_of_seq. apply (eq_trans (eq_sym Heqb)). simpl. exact IsomorphismDefinitions.eq_refl. }
    rewrite E2. simpl.
    constructor. simpl. unfold option_to_imported.
    exact (IsoEq.f_equal (Imported.option_Some x2) H78).
  - (* k1 <> x1' in Coq, so String_eqb k2 x2' should be mybool_myfalse *)
    assert (Imported.String_eqb x6 x10 = Imported.mybool_myfalse) as E2.
    { apply eq_of_seq. apply (eq_trans (eq_sym Heqb)). simpl. exact IsomorphismDefinitions.eq_refl. }
    rewrite E2. simpl.
    apply Hmap. exact H910.
Defined.
Instance: KnownConstant (@Original.LF_DOT_Maps.LF.Maps.update) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Original_LF__DOT__Maps_LF_Maps_update) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF_DOT_Maps.LF.Maps.update) Original_LF__DOT__Maps_LF_Maps_update_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_Maps.LF.Maps.update) (@Imported.Original_LF__DOT__Maps_LF_Maps_update) Original_LF__DOT__Maps_LF_Maps_update_iso := {}.
