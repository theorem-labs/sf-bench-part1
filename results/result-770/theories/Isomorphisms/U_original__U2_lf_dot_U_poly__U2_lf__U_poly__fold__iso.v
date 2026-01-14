From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.

Definition imported_Original_LF__DOT__Poly_LF_Poly_fold : forall x x0 : Type, (x -> x0 -> x0) -> imported_Original_LF__DOT__Poly_LF_Poly_list x -> x0 -> x0 := (@Imported.Original_LF__DOT__Poly_LF_Poly_fold).
Instance Original_LF__DOT__Poly_LF_Poly_fold_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 x4 : Type) (hx0 : IsoOrSortRelaxed x3 x4) (x5 : x1 -> x3 -> x3) (x6 : x2 -> x4 -> x4),
  (forall (x7 : x1) (x8 : x2), rel_iso hx x7 x8 -> forall (x9 : x3) (x10 : x4), rel_iso_sort hx0 x9 x10 -> rel_iso_sort hx0 (x5 x7 x9) (x6 x8 x10)) ->
  forall (x7 : Original.LF_DOT_Poly.LF.Poly.list x1) (x8 : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x7 x8 ->
  forall (x9 : x3) (x10 : x4), rel_iso_sort hx0 x9 x10 -> rel_iso_sort hx0 (Original.LF_DOT_Poly.LF.Poly.fold x5 x7 x9) (imported_Original_LF__DOT__Poly_LF_Poly_fold x6 x8 x10).
Proof.
  intros x1 x2 hx x3 x4 hx0 x5 x6 Hf x7 x8 H78 x9 x10 H910.
  unfold rel_iso in H78.
  simpl in H78.
  revert x8 H78 x9 x10 H910.
  induction x7 as [|h t IH]; intros x8 H78 x9 x10 H910.
  - (* nil case *)
    simpl.
    unfold imported_Original_LF__DOT__Poly_LF_Poly_fold.
    assert (Heq : x8 = Imported.Original_LF__DOT__Poly_LF_Poly_list_nil x2).
    { symmetry. apply (IsoEq.eq_of_seq H78). }
    rewrite Heq.
    simpl.
    exact H910.
  - (* cons case *)
    simpl.
    unfold imported_Original_LF__DOT__Poly_LF_Poly_fold.
    assert (Heq : x8 = Imported.Original_LF__DOT__Poly_LF_Poly_list_cons x2 (to hx h) (to (Original_LF__DOT__Poly_LF_Poly_list_iso hx) t)).
    { symmetry. apply (IsoEq.eq_of_seq H78). }
    rewrite Heq.
    simpl.
    apply Hf.
    + unfold rel_iso. apply IsomorphismDefinitions.eq_refl.
    + apply IH.
      * unfold rel_iso. apply IsomorphismDefinitions.eq_refl.
      * exact H910.
Defined.
Instance: KnownConstant (@Original.LF_DOT_Poly.LF.Poly.fold) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Original_LF__DOT__Poly_LF_Poly_fold) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF_DOT_Poly.LF.Poly.fold) Original_LF__DOT__Poly_LF_Poly_fold_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_Poly.LF.Poly.fold) (@Imported.Original_LF__DOT__Poly_LF_Poly_fold) Original_LF__DOT__Poly_LF_Poly_fold_iso := {}.