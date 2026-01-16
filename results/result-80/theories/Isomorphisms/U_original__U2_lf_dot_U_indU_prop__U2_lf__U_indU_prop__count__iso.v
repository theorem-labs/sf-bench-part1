From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Isomorphisms.nat__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__eqb__iso.

Monomorphic Definition imported_Original_LF__DOT__IndProp_LF_IndProp_count : imported_nat -> imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat -> imported_nat := Imported.Original_LF__DOT__IndProp_LF_IndProp_count.
Monomorphic Instance Original_LF__DOT__IndProp_LF_IndProp_count_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 ->
  forall (x3 : Original.LF_DOT_Poly.LF.Poly.list nat) (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso nat_iso) x3 x4 -> rel_iso nat_iso (Original.LF_DOT_IndProp.LF.IndProp.count x1 x3) (imported_Original_LF__DOT__IndProp_LF_IndProp_count x2 x4).
Proof.
  intros n1 n2 Hn.
  fix IH 1.
  intros x3 x4 Hx.
  destruct Hx as [Hx].
  constructor. simpl.
  unfold imported_Original_LF__DOT__IndProp_LF_IndProp_count.
  simpl in *.
  destruct x3 as [| h t].
  - (* nil case *)
    apply (@IsoEq.eq_srect_nodep _ (Imported.Original_LF__DOT__Poly_LF_Poly_list_nil imported_nat) (fun y => IsomorphismDefinitions.eq (Imported.nat_O) (Imported.Original_LF__DOT__IndProp_LF_IndProp_count n2 y)) IsomorphismDefinitions.eq_refl x4 Hx).
  - (* cons case *)
    simpl.
    assert (Heqb : IsomorphismDefinitions.eq (to Original_LF__DOT__Basics_LF_Basics_bool_iso (Original.LF_DOT_Basics.LF.Basics.eqb n1 h)) (Imported.Original_LF__DOT__Basics_LF_Basics_eqb n2 (to nat_iso h))).
    { pose proof (@Original_LF__DOT__Basics_LF_Basics_eqb_iso n1 n2 Hn h (to nat_iso h) ltac:(constructor; apply IsomorphismDefinitions.eq_refl)) as H.
      destruct H as [H]. exact H. }
    apply (@IsoEq.eq_srect_nodep _ (Imported.Original_LF__DOT__Poly_LF_Poly_list_cons imported_nat (to nat_iso h) (to (Original_LF__DOT__Poly_LF_Poly_list_iso nat_iso) t)) (fun y => IsomorphismDefinitions.eq 
        (to nat_iso ((if Original.LF_DOT_Basics.LF.Basics.eqb n1 h then 1 else 0) + Original.LF_DOT_IndProp.LF.IndProp.count n1 t))
        (Imported.Original_LF__DOT__IndProp_LF_IndProp_count n2 y))).
    + apply (@IsoEq.eq_srect_r _ (to Original_LF__DOT__Basics_LF_Basics_bool_iso (Original.LF_DOT_Basics.LF.Basics.eqb n1 h))
        (fun b => IsomorphismDefinitions.eq
          (to nat_iso ((if Original.LF_DOT_Basics.LF.Basics.eqb n1 h then 1 else 0) + Original.LF_DOT_IndProp.LF.IndProp.count n1 t))
          (Imported.Original_LF__DOT__Poly_LF_Poly_filter_match_1 (fun _ => _) b _ _))).
      * destruct (Original.LF_DOT_Basics.LF.Basics.eqb n1 h); simpl.
        -- (* true case: 1 + count = S count *)
           apply (IsoEq.f_equal (Imported.nat_S)).
           pose proof (IH t (to (Original_LF__DOT__Poly_LF_Poly_list_iso nat_iso) t) ltac:(constructor; apply IsomorphismDefinitions.eq_refl)) as IHt.
           destruct IHt as [IHt]. exact IHt.
        -- (* false case: 0 + count = count *)
           pose proof (IH t (to (Original_LF__DOT__Poly_LF_Poly_list_iso nat_iso) t) ltac:(constructor; apply IsomorphismDefinitions.eq_refl)) as IHt.
           destruct IHt as [IHt]. exact IHt.
      * exact (IsoEq.eq_sym Heqb).
    + exact Hx.
Defined.
Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.count := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_count := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.count Original_LF__DOT__IndProp_LF_IndProp_count_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.count Imported.Original_LF__DOT__IndProp_LF_IndProp_count Original_LF__DOT__IndProp_LF_IndProp_count_iso := {}.