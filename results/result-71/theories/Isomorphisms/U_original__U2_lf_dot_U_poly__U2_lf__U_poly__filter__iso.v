From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.

Definition imported_Original_LF__DOT__Poly_LF_Poly_filter : forall x : Type, (x -> imported_Original_LF__DOT__Basics_LF_Basics_bool) -> imported_Original_LF__DOT__Poly_LF_Poly_list x -> imported_Original_LF__DOT__Poly_LF_Poly_list x := (@Imported.Original_LF__DOT__Poly_LF_Poly_filter).

(* Helper lemma: computational equivalence of filter *)
Lemma filter_iso_helper :
  forall (x1 x2 : Type) (hx : Iso x1 x2) 
         (test1 : x1 -> Original.LF_DOT_Basics.LF.Basics.bool) 
         (test2 : x2 -> imported_Original_LF__DOT__Basics_LF_Basics_bool),
  (forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso (test1 x5) (test2 x6)) ->
  forall (l1 : Original.LF_DOT_Poly.LF.Poly.list x1),
  IsomorphismDefinitions.eq 
    (list_to_imported hx (Original.LF_DOT_Poly.LF.Poly.filter test1 l1))
    (Imported.Original_LF__DOT__Poly_LF_Poly_filter x2 test2 (list_to_imported hx l1)).
Proof.
  intros x1 x2 hx test1 test2 Htest.
  fix IH 1.
  intros l1.
  destruct l1 as [|h t].
  - (* nil case *)
    simpl. apply IsomorphismDefinitions.eq_refl.
  - (* cons case *)
    simpl.
    assert (Htest_h : rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso (test1 h) (test2 (hx h))).
    { apply Htest. constructor. apply IsomorphismDefinitions.eq_refl. }
    destruct Htest_h as [Htest_h].
    simpl in Htest_h.
    destruct (test1 h) eqn:Htest1h.
    + (* test1 h = true *)
      simpl.
      apply (@IsoEq.eq_srect_nodep _ (bool_to_imported Original.LF_DOT_Basics.LF.Basics.true) (fun b => IsomorphismDefinitions.eq
             (Imported.Original_LF__DOT__Poly_LF_Poly_list_cons x2 (hx h) (list_to_imported hx (Original.LF_DOT_Poly.LF.Poly.filter test1 t)))
             (if b then Imported.Original_LF__DOT__Poly_LF_Poly_list_cons x2 (hx h) (Imported.Original_LF__DOT__Poly_LF_Poly_filter x2 test2 (list_to_imported hx t)) else Imported.Original_LF__DOT__Poly_LF_Poly_filter x2 test2 (list_to_imported hx t)))).
      * simpl.
        apply (IsoEq.f_equal2 (Imported.Original_LF__DOT__Poly_LF_Poly_list_cons x2)).
        -- apply IsomorphismDefinitions.eq_refl.
        -- apply IH.
      * exact Htest_h.
    + (* test1 h = false *)
      simpl.
      apply (@IsoEq.eq_srect_nodep _ (bool_to_imported Original.LF_DOT_Basics.LF.Basics.false) (fun b => IsomorphismDefinitions.eq
             (list_to_imported hx (Original.LF_DOT_Poly.LF.Poly.filter test1 t))
             (if b then Imported.Original_LF__DOT__Poly_LF_Poly_list_cons x2 (hx h) (Imported.Original_LF__DOT__Poly_LF_Poly_filter x2 test2 (list_to_imported hx t)) else Imported.Original_LF__DOT__Poly_LF_Poly_filter x2 test2 (list_to_imported hx t)))).
      * simpl. apply IH.
      * exact Htest_h.
Qed.

Instance Original_LF__DOT__Poly_LF_Poly_filter_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1 -> Original.LF_DOT_Basics.LF.Basics.bool) (x4 : x2 -> imported_Original_LF__DOT__Basics_LF_Basics_bool),
  (forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso (x3 x5) (x4 x6)) ->
  forall (x5 : Original.LF_DOT_Poly.LF.Poly.list x1) (x6 : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x5 x6 ->
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) (Original.LF_DOT_Poly.LF.Poly.filter x3 x5) (imported_Original_LF__DOT__Poly_LF_Poly_filter x4 x6).
Proof.
  intros x1 x2 hx test1 test2 Htest l1 l2 Hl.
  destruct Hl as [Hl].
  constructor.
  eapply eq_trans.
  - apply filter_iso_helper. exact Htest.
  - apply IsoEq.f_equal. exact Hl.
Defined.

Instance: KnownConstant (@Original.LF_DOT_Poly.LF.Poly.filter) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Original_LF__DOT__Poly_LF_Poly_filter) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF_DOT_Poly.LF.Poly.filter) Original_LF__DOT__Poly_LF_Poly_filter_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_Poly.LF.Poly.filter) (@Imported.Original_LF__DOT__Poly_LF_Poly_filter) Original_LF__DOT__Poly_LF_Poly_filter_iso := {}.
