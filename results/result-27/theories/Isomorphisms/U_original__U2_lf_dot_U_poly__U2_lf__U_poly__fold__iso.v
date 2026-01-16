From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
From IsomorphismChecker Require Original Imported.
#[local] Set Printing Coercions.

From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.

Monomorphic Definition imported_Original_LF__DOT__Poly_LF_Poly_fold : forall x x0 : Type, (x -> x0 -> x0) -> imported_Original_LF__DOT__Poly_LF_Poly_list x -> x0 -> x0 := (@Imported.Original_LF__DOT__Poly_LF_Poly_fold).

(* Imported.fold satisfies the nil reduction *)
Lemma imported_fold_nil : forall (X Y : Type) (f : X -> Y -> Y) (b : Y),
  Imported.Original_LF__DOT__Poly_LF_Poly_fold X Y f (Imported.Original_LF__DOT__Poly_LF_Poly_nil X) b = b.
Proof. intros. reflexivity. Qed.

(* Imported.fold satisfies the cons reduction *)
Lemma imported_fold_cons : forall (X Y : Type) (f : X -> Y -> Y) (h : X) (t : Imported.Original_LF__DOT__Poly_LF_Poly_list X) (b : Y),
  Imported.Original_LF__DOT__Poly_LF_Poly_fold X Y f (Imported.Original_LF__DOT__Poly_LF_Poly_cons X h t) b = 
  f h (Imported.Original_LF__DOT__Poly_LF_Poly_fold X Y f t b).
Proof. intros. reflexivity. Qed.

Monomorphic Instance Original_LF__DOT__Poly_LF_Poly_fold_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 x4 : Type) (hx0 : IsoOrSortRelaxed x3 x4) (x5 : x1 -> x3 -> x3) (x6 : x2 -> x4 -> x4),
  (forall (x7 : x1) (x8 : x2), rel_iso hx x7 x8 -> forall (x9 : x3) (x10 : x4), rel_iso_sort hx0 x9 x10 -> rel_iso_sort hx0 (x5 x7 x9) (x6 x8 x10)) ->
  forall (x7 : Original.LF_DOT_Poly.LF.Poly.list x1) (x8 : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x7 x8 ->
  forall (x9 : x3) (x10 : x4), rel_iso_sort hx0 x9 x10 -> rel_iso_sort hx0 (Original.LF_DOT_Poly.LF.Poly.fold x5 x7 x9) (imported_Original_LF__DOT__Poly_LF_Poly_fold x6 x8 x10).
Proof.
  intros x1 x2 hx x3 x4 hx0 x5 x6 Hf.
  induction x7 as [| h t IH]; intros x8 [Hlist] x9 x10 Hbase.
  - (* nil case *)
    simpl in Hlist. apply eq_of_seq in Hlist. subst x8.
    simpl. unfold imported_Original_LF__DOT__Poly_LF_Poly_fold. rewrite imported_fold_nil.
    exact Hbase.
  - (* cons case *)
    simpl in Hlist. apply eq_of_seq in Hlist. subst x8.
    simpl. unfold imported_Original_LF__DOT__Poly_LF_Poly_fold. rewrite imported_fold_cons.
    apply Hf.
    + apply rel_iso_refl.
    + apply IH.
      * constructor. apply IsomorphismDefinitions.eq_refl.
      * exact Hbase.
Defined.

Instance: KnownConstant (@Original.LF_DOT_Poly.LF.Poly.fold) := {}.
Instance: KnownConstant (@Imported.Original_LF__DOT__Poly_LF_Poly_fold) := {}.
Instance: IsoStatementProofFor (@Original.LF_DOT_Poly.LF.Poly.fold) Original_LF__DOT__Poly_LF_Poly_fold_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_Poly.LF.Poly.fold) (@Imported.Original_LF__DOT__Poly_LF_Poly_fold) Original_LF__DOT__Poly_LF_Poly_fold_iso := {}.
