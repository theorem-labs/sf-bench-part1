From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
(* Typeclasses Opaque rel_iso. *) (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__partial____map__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update__iso.

Definition imported_Original_LF__DOT__Maps_LF_Maps_update : forall x : Type, (imported_String_string -> imported_option x) -> imported_String_string -> x -> imported_String_string -> imported_option x := (@Imported.Original_LF__DOT__Maps_LF_Maps_update).

(* Helper lemma for Some values - use WrapSProp directly *)
Lemma option_Some_iso_helper : forall (x1 x2 : Type) (hx : Iso x1 x2) (v1 : x1) (v2 : x2),
  rel_iso hx v1 v2 ->
  WrapSProp (rel_iso (option_iso hx) (Some v1) (Imported.option_Some x2 v2)).
Proof.
  intros x1 x2 hx v1 v2 Hv.
  constructor.
  constructor.
  simpl.
  apply IsoEq.f_equal.
  exact (proj_rel_iso Hv).
Defined.

Instance Original_LF__DOT__Maps_LF_Maps_update_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_Maps.LF.Maps.partial_map x1) (x4 : imported_String_string -> imported_option x2),
  (forall (x5 : String.string) (x6 : imported_String_string), rel_iso String_string_iso x5 x6 -> rel_iso (option_iso hx) (x3 x5) (x4 x6)) ->
  forall (x5 : String.string) (x6 : imported_String_string),
  rel_iso String_string_iso x5 x6 ->
  forall (x7 : x1) (x8 : x2),
  rel_iso hx x7 x8 ->
  forall (x9 : String.string) (x10 : imported_String_string),
  rel_iso String_string_iso x9 x10 -> rel_iso (option_iso hx) (Original.LF_DOT_Maps.LF.Maps.update x3 x5 x7 x9) (imported_Original_LF__DOT__Maps_LF_Maps_update x4 x6 x8 x10).
Proof.
  intros x1 x2 hx m1 m2 Hm k1 k2 Hk v1 v2 Hv x1' x2' Hx.
  unfold Original.LF_DOT_Maps.LF.Maps.update, imported_Original_LF__DOT__Maps_LF_Maps_update.
  unfold Imported.Original_LF__DOT__Maps_LF_Maps_update.
  apply (@Original_LF__DOT__Maps_LF_Maps_t__update_iso _ _ (option_iso hx) m1 m2).
  - intros s1 s2 Hs.
    exact {| unwrap_sprop := Hm s1 s2 Hs |}.
  - exact Hk.
  - exact (@option_Some_iso_helper x1 x2 hx v1 v2 Hv).
  - exact Hx.
Defined.
Instance: KnownConstant (@Original.LF_DOT_Maps.LF.Maps.update) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Original_LF__DOT__Maps_LF_Maps_update) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF_DOT_Maps.LF.Maps.update) Original_LF__DOT__Maps_LF_Maps_update_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_Maps.LF.Maps.update) (@Imported.Original_LF__DOT__Maps_LF_Maps_update) Original_LF__DOT__Maps_LF_Maps_update_iso := {}.
